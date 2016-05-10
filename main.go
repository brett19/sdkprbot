package main

import (
	"crypto/rand"
	"crypto/sha1"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"github.com/brett19/go-gerrit"
	"github.com/google/go-github/github"
	"github.com/gregjones/httpcache"
	"github.com/knakk/digest"
	"gopkg.in/libgit2/git2go.v23"
	"golang.org/x/oauth2"
	"io/ioutil"
	"log"
	"net/http"
	"os"
	"regexp"
	"strings"
	"time"
	"strconv"
)

var isDryRun bool = true

const BOT_IDENT_TAG = "::SDKBOT/PR"

func RandomChangeId() string {
	b := make([]byte, sha1.Size)
	rand.Read(b)
	encData := sha1.Sum(b)
	return "I" + hex.EncodeToString(encData[:])
}

type subError struct {
	msg string
	err error
}

func (e subError) Error() string {
	if e.err != nil {
		return e.msg + ": " + e.err.Error()
	} else {
		return e.msg
	}
}

func makeErr(msg string, err error) error {
	return subError{msg, err}
}

func SquashHead(repo *git.Repository, squashCount int, mergeCommitTitle, changeId string) error {
	log.Printf("Generating squash commit for `HEAD~0` to `HEAD~%d`", squashCount)

	headRef, err := repo.Head()
	if err != nil {
		return makeErr("failed to get head reference", err)
	}

	topCommitId := headRef.Target()
	topCommit, err := repo.LookupCommit(topCommitId)
	if err != nil {
		return makeErr("failed to locate head commit", nil)
	}

	var baseCommit *git.Commit

	var squashCommits []*git.Commit
	{
		curCommit := topCommit
		for i := 0; i < squashCount; i++ {
			squashCommits = append(squashCommits, curCommit)

			curCommit = curCommit.Parent(0)
		}
		baseCommit = curCommit
	}

	log.Printf("Base Commit is `%s`", baseCommit.Id().String())

	var newCommitAuthor *git.Signature
	var newCommitCommitter *git.Signature
	var newCommitMsg string

	if len(squashCommits) == 1 {
		newCommitAuthor = squashCommits[0].Author()
		newCommitCommitter = squashCommits[0].Committer()
		newCommitMsg = strings.TrimSpace(squashCommits[0].Message()) + "\n"
	} else {
		newCommitMsg = ""
		newCommitMsg += mergeCommitTitle + "\n\n"

		for i := 0; i < len(squashCommits); i++ {
			curCommit := squashCommits[i]

			newCommitMsg += "----\n"
			newCommitMsg += strings.TrimSpace(curCommit.Message()) + "\n"

			newCommitAuthor = curCommit.Author()
			newCommitCommitter = curCommit.Committer()
		}
	}

	newCommitMsg += "\nChange-Id: " + changeId

	err = repo.ResetToCommit(baseCommit, git.ResetSoft, nil)
	if err != nil {
		return makeErr("failed to reset to base commit", err)
	}

	idx, err := repo.Index()
	if err != nil {
		return makeErr("failed to retrieve repo index", err)
	}

	err = idx.Write()
	if err != nil {
		return makeErr("failed to write squash index", err)
	}

	newCommitTreeId, err := idx.WriteTree()
	if err != nil {
		return makeErr("failed to write squash tree", err)
	}

	newCommitTree, err := repo.LookupTree(newCommitTreeId)
	if err != nil {
		return makeErr("failed to find created squash tree", err)
	}

	log.Printf("Generated new commit message:\n%s", newCommitMsg)

	_, err = repo.CreateCommit("HEAD", newCommitAuthor, newCommitCommitter, newCommitMsg, newCommitTree, baseCommit)
	if err != nil {
		return makeErr("failed to generate squash commit", err)
	}

	return nil
}

type CsStateInfo struct {
	ChangeNum   int
	ChangeId    string
	Status      string
	CurrentSha1 string
}

func GetChangesetState(owner, repo string, prnum int) (*CsStateInfo, error) {
	log.Printf("Retrieving change set for %s/%s/%d", owner, repo, prnum)

	path := fmt.Sprintf("github.com/%s/%s/pull/%d", owner, repo, prnum)

	changes, _, err := gerritClient.Changes.QueryChanges(&gerrit.QueryChangeOptions{
		QueryOptions: gerrit.QueryOptions{
			Query: []string{path},
		},
		ChangeOptions: gerrit.ChangeOptions{
			AdditionalFields: []string{"messages"},
		},
	})
	if err != nil {
		return nil, makeErr("failed to gerrit query for changes", err)
	}

	var foundChangeset *gerrit.ChangeInfo
	for i := 0; i < len(*changes); i++ {
		change := &(*changes)[i]

		for j := 0; j < len(change.Messages); j++ {
			if !strings.Contains(change.Messages[j].Message, BOT_IDENT_TAG) {
				continue
			}

			if strings.Contains(change.Messages[j].Message, path) {
				if foundChangeset != nil {
					return nil, makeErr("found multiple possible changesets", nil)
				}

				foundChangeset = change
				break
			}
		}
	}

	if foundChangeset == nil {
		return nil, nil
	}

	commitMatcher, err := regexp.Compile("commit:([0-9a-zA-Z]+)")
	if err != nil {
		return nil, makeErr("failed to compile commit sha1 finding regexp", err)
	}

	var latestSha1 string

	for i := 0; i < len(foundChangeset.Messages); i++ {
		commitMatches := commitMatcher.FindStringSubmatch(foundChangeset.Messages[i].Message)
		if len(commitMatches) == 2 {
			latestSha1 = commitMatches[1]
		}
	}

	return &CsStateInfo{
		ChangeNum:   foundChangeset.Number,
		ChangeId:    foundChangeset.ChangeID,
		Status:      foundChangeset.Status,
		CurrentSha1: latestSha1,
	}, nil
}

type RepoInfo struct {
	Owner string
	Name  string
	Repo  string
}

var botOwners []string
var githubClient *github.Client
var githubUser string
var githubToken string
var gerritClient *gerrit.Client
var gerritHost string
var gerritUser string
var gerritPass string
var gerritPublicKey string
var gerritPrivateKey string
var gerritClaGroupName string
var allRepos []RepoInfo

func gerritGitCredentialsHandler(url string, username_from_url string, allowed_types git.CredType) (git.ErrorCode, *git.Cred) {
	errCode, creds := git.NewCredSshKey(gerritUser, gerritPublicKey, gerritPrivateKey, "")
	return git.ErrorCode(errCode), &creds
}

func initGerritClient() error {
	tc, err := digest.NewTransport(gerritUser, gerritPass).Client()
	if err != nil {
		return makeErr("failed to create gerrit digest client", err)
	}

	client, err := gerrit.NewClient("http://"+gerritHost+"/", tc)
	if err != nil {
		return makeErr("failed to create gerrit client", err)
	}

	client.Authentication.SetBasicAuth(gerritUser, "")

	gerritClient = client
	return nil
}

func initGitHubClient() error {
	tx := httpcache.NewMemoryCacheTransport()

	tc := &http.Client{
		Transport: &oauth2.Transport{
			Source: oauth2.StaticTokenSource(
				&oauth2.Token{AccessToken: githubToken},
			),
			Base: tx,
		},
	}

	githubClient = github.NewClient(tc)
	return nil
}

type PrStateInfo struct {
	CurrentState    string
	LastUpdatedTime time.Time
	CurrentSha1     string
	NumOfCommits    int
}

func IsGitHubUserBot(user *github.User) bool {
	if user == nil || user.Login == nil {
		return false
	}

	if *user.Login == githubUser {
		return true
	}
	return false
}

func IsGitHubUserBotOwner(user *github.User) bool {
	if user == nil || user.Login == nil {
		return false
	}

	for i := 0; i < len(botOwners); i++ {
		if *user.Login == botOwners[i] {
			return true
		}
	}
	return IsGitHubUserBot(user)
}

const (
	BOTSTATE_NEW       = ""
	BOTSTATE_NO_CLA    = "no_cla"
	BOTSTATE_CREATED   = "created"
	BOTSTATE_UPDATED   = "updated"
	BOTSTATE_ABANDONED = "abandoned"
	BOTSTATE_MERGED    = "merged"
	BOTSTATE_TIMEOUT   = "timeout"
)

func GetPullRequestState(owner, repo string, prnum int) (*PrStateInfo, error) {
	var parseableStateNames = []string{
		BOTSTATE_NO_CLA,
		BOTSTATE_CREATED,
		BOTSTATE_UPDATED,
		BOTSTATE_ABANDONED,
		BOTSTATE_MERGED,
		BOTSTATE_TIMEOUT,

		// backwards compatibility names
		"pushed",
		"too_many_commits",
		"closed",
	}

	log.Printf("Retrieving PR state for %s/%s/%d", owner, repo, prnum)

	info, _, err := githubClient.PullRequests.Get(owner, repo, prnum)
	if err != nil {
		return nil, makeErr("failed to retieve pull request info", err)
	}

	comments, _, err := githubClient.Issues.ListComments(owner, repo, prnum, nil)
	if err != nil {
		return nil, makeErr("failed to retrieve pull request comments", err)
	}

	var lastStateTime time.Time
	var lastStateName string
	var lastUpdatedTime time.Time

	for i := 0; i < len(comments); i++ {
		if comments[i].CreatedAt.After(lastUpdatedTime) || comments[i].UpdatedAt.After(lastUpdatedTime) {
			lastUpdatedTime = *comments[i].UpdatedAt
		}

		if !IsGitHubUserBotOwner(comments[i].User) {
			continue
		}

		for j := 0; j < len(parseableStateNames); j++ {
			if strings.Contains(*comments[i].Body, BOT_IDENT_TAG+":"+parseableStateNames[j]) {
				if comments[i].CreatedAt.After(lastStateTime) {
					lastStateName = parseableStateNames[j]
					lastStateTime = *comments[i].CreatedAt
				}
			}
		}
	}

	// For backwards compat...
	if lastStateName == "too_many_commits" {
		lastStateName = BOTSTATE_NEW
	} else if lastStateName == "pushed" {
		lastStateName = BOTSTATE_UPDATED
	} else if lastStateName == "closed" {
		lastStateName = BOTSTATE_ABANDONED
	}

	if lastUpdatedTime.IsZero() {
		lastUpdatedTime = time.Now()
	}

	return &PrStateInfo{
		CurrentState:    lastStateName,
		LastUpdatedTime: lastUpdatedTime,
		CurrentSha1:     *info.Head.SHA,
		NumOfCommits:    *info.Commits,
	}, nil
}

func VerifyEmailCla(email string) (bool, error) {
	log.Printf("Verifying CLA signed for `%s`", email)

	groups, _, err := gerritClient.Accounts.ListGroups(email)

	if err != nil {
		if strings.Contains(err.Error(), "Not Found") {
			log.Printf("Email was not found on Gerrit")
			return false, nil
		}

		log.Printf("An error occured trying to locate the user on Gerrit")
		return false, makeErr("failed to retrieve gerrit user groups", err)
	}

	hasClaGroup := false
	for i := 0; i < len(*groups); i++ {
		if (*groups)[i].Name == gerritClaGroupName {
			hasClaGroup = true
		}
	}

	if hasClaGroup {
		log.Printf("The user was located and has signed the CLA")
	} else {
		log.Printf("The user was located, but they did not sign the CLA")
	}
	return hasClaGroup, nil
}

func VerifyPrAuthorClas(owner, repo string, prnum int) (bool, error) {
	log.Printf("Verifying CLA signed for PR %s/%s/%d", owner, repo, prnum)

	commits, _, err := githubClient.PullRequests.ListCommits(owner, repo, prnum, nil)
	if err != nil {
		return false, makeErr("failed to retrieve pull request commits", err)
	}

	authorEmailMap := make(map[string]bool)

	for i := 0; i < len(commits); i++ {
		authorEmail := *commits[i].Commit.Author.Email
		authorEmailMap[authorEmail] = false
	}

	allSigned := true
	for authorEmail, _ := range authorEmailMap {
		signed, err := VerifyEmailCla(authorEmail)
		if err != nil {
			return false, err
		}

		if !signed {
			allSigned = false
		}
	}

	return allSigned, nil
}

func SendPrStateCommentAndClose(owner, repo string, prnum int, message, state string, is_first bool) error {
	if isDryRun {
		log.Printf("Skipping pr comment and close for '%s' due to dry run.", state)
		return nil
	}

	newState := "closed"
	_, _, err := githubClient.PullRequests.Edit(owner, repo, prnum, &github.PullRequest{
		State: &newState,
	})
	if err != nil {
		return makeErr("failed to close pull request", err)
	}

	return SendPrStateComment(owner, repo, prnum, message, state, is_first)
}

func SendPrStateComment(owner, repo string, prnum int, message, state string, is_first bool) error {
	if isDryRun {
		log.Printf("Skipping pr comment for '%s' due to dry run.", state)
		return nil
	}

	var messageBody string

	if is_first {
		messageBody += "Thanks for the pull request!!  To ensure quality review, Couchbase employs"
		messageBody += " a [code review system](http://review.couchbase.org/) based on"
		messageBody += " [Gerrit](https://www.gerritcodereview.com/) to manage the workflow of changes"
		messageBody += " in addition to tracking our contributor agreements.\n\n"
	}
	messageBody += strings.TrimSpace(message)
	messageBody += "\n\n" + BOT_IDENT_TAG + ":" + state

	_, _, err := githubClient.Issues.CreateComment(owner, repo, prnum, &github.IssueComment{
		Body: &messageBody,
	})
	if err != nil {
		return makeErr("failed to comment on pull request", err)
	}

	return nil
}

func SendClaText(owner, repo string, prnum int, state *PrStateInfo) error {
	log.Printf("Sending no_cla for %s/%s/%d", owner, repo, prnum)

	message := "To get this change in and collaborate in code review, please register on Gerrit"
	message += " and accept our CLA.  The easiest way to do this is to follow the link below,"
	message += " sign in with your GitHub account and then follow through the steps provided"
	message += " on that page to sign an 'Individual' agreement:"
	message += " http://review.couchbase.org/#/settings/new-agreement."
	message += "\n\n"
	message += "Note: Please contact us if you have any issues registering with Gerrit!"
	message += " If you have not signed our CLA within 7 days, the Pull Request will be"
	message += " automatically closed."

	return SendPrStateComment(owner, repo, prnum, message, BOTSTATE_NO_CLA, state.CurrentState == BOTSTATE_NEW)
}

func SendPushedText(owner, repo string, prnum int, state *PrStateInfo, changeNum int) error {
	log.Printf("Sending pushed for %s/%s/%d", owner, repo, prnum)

	message := "Your changes (commit: " + state.CurrentSha1 + ") have been pushed to the Couchbase Review Site:\n"
	message += "http://review.couchbase.org/" + strconv.FormatInt(int64(changeNum), 10)

	if state.NumOfCommits > 1 {
		message += "\n\n"
		message += "Note: As your pull request contains multiple commits, we have"
		message += " performed an automatic squash of these commits into a single"
		message += " change-set.  If this is not the desired behaviour, please"
		message += " consider submitting a pull request per discreet feature."
	}

	if state.CurrentState == BOTSTATE_CREATED || state.CurrentState == BOTSTATE_UPDATED {
		return SendPrStateComment(owner, repo, prnum, message, BOTSTATE_UPDATED, false)
	} else {
		return SendPrStateComment(owner, repo, prnum, message, BOTSTATE_CREATED, state.CurrentState == BOTSTATE_NEW)
	}
}

func ClosePrForTimeout(owner, repo string, prnum int, state *PrStateInfo) error {
	log.Printf("Closing due to timeout for %s/%s/%d", owner, repo, prnum)

	message := "Unfortunately it has been 7 days and we are still unable to confirm that you"
	message += " have signed our CLA.  We sincerely appreciate your submission and hope that"
	message += " you will register and resubmit this Pull Request in the future!"

	return SendPrStateCommentAndClose(owner, repo, prnum, message, BOTSTATE_TIMEOUT, state.CurrentState == BOTSTATE_NEW)
}

func ClosePrForMerge(owner, repo string, prnum int, state *PrStateInfo) error {
	log.Printf("Closing due to gerrit merge for %s/%s/%d", owner, repo, prnum)

	message := "This Pull Request has been closed as the associated Gerrit change was merged."

	return SendPrStateCommentAndClose(owner, repo, prnum, message, BOTSTATE_MERGED, state.CurrentState == BOTSTATE_NEW)
}

func ClosePrForAbandon(owner, repo string, prnum int, state *PrStateInfo) error {
	log.Printf("Closing due to gerrit abandon for %s/%s/%d", owner, repo, prnum)

	message := "This Pull Request has been closed as the associated Gerrit change was abandoned."

	return SendPrStateCommentAndClose(owner, repo, prnum, message, BOTSTATE_ABANDONED, state.CurrentState == BOTSTATE_NEW)
}

func GetGerritRepo(owner, repo string) string {
	return repo
}

func TransferPrToGerrit(owner, repo string, prnum int, prstate *PrStateInfo) error {
	log.Printf("Attempting to gerrit transfer PR %s/%s/%d %v", owner, repo, prnum, prstate)

	csstate, err := GetChangesetState(owner, repo, prnum)
	if err != nil {
		return err
	}

	if csstate != nil {
		if csstate.Status == "ABANDONED" {
			return ClosePrForAbandon(owner, repo, prnum, prstate)
		}
		if csstate.Status == "MERGED" {
			return ClosePrForMerge(owner, repo, prnum, prstate)
		}
		if csstate.CurrentSha1 == prstate.CurrentSha1 {
			// Already up to date!
			log.Printf("Nothing to do, already up to date.")
			return nil
		}
	}

	thisChangeId := RandomChangeId()
	if csstate != nil {
		thisChangeId = csstate.ChangeId
	}

	pr, _, err := githubClient.PullRequests.Get(owner, repo, prnum)
	if err != nil {
		return makeErr("failed to request pull request data", err)
	}

	gitRepoPath := "/tmp/gtest"

	os.RemoveAll(gitRepoPath)

	gitRepo, err := git.Clone(*pr.Head.Repo.CloneURL, gitRepoPath, &git.CloneOptions{
		CheckoutBranch: *pr.Head.Ref,
	})
	if err != nil {
		return makeErr("failed to clone repository head", err)
	}

	err = SquashHead(gitRepo, *pr.Commits, *pr.Title, thisChangeId)
	if err != nil {
		return err
	}

	log.Printf("Generated squash commit with ChangeId `%s`", thisChangeId)

	if isDryRun {
		log.Printf("Skipping remote push and comment due to dry run.")
		return nil
	}

	reviewRemote, err := gitRepo.Remotes.Create("review",
		"ssh://"+gerritUser+"@"+gerritHost+":29418/"+GetGerritRepo(owner, repo))
	if err != nil {
		return makeErr("failed to add gerrit as a remote", err)
	}

	log.Printf("Assigned remote.")

	statusText := ""
	err = reviewRemote.Push([]string{"HEAD:refs/for/master"}, &git.PushOptions{
		RemoteCallbacks: git.RemoteCallbacks{
			PushUpdateReferenceCallback: func(refname, status string) git.ErrorCode {
				statusText = status
				return 0
			},
			CredentialsCallback: gerritGitCredentialsHandler,
			CertificateCheckCallback: func(cert *git.Certificate, valid bool, hostname string) git.ErrorCode {
				return 0
			},
		},
	})
	if err != nil {
		return makeErr("failed to push to gerrit", err)
	}

	log.Printf("Successfully pushed to Gerrit with status `%s`", statusText)

	if statusText != "" {
		if statusText == "no new changes" && prstate != nil &&
		(prstate.CurrentState == BOTSTATE_CREATED || prstate.CurrentState == BOTSTATE_UPDATED) {
			// Nothing changed
			return nil
		}

		return makeErr("failed to upload to gerrit", errors.New(statusText))
	}

	var reviewMessage string
	reviewMessage += fmt.Sprintf("Change-Set generated from https://github.com/%s/%s/pull/%d (commit:%s).",
		owner, repo, prnum, *pr.Head.SHA)
	reviewMessage += "\n" + BOT_IDENT_TAG

	_, _, err = gerritClient.Changes.SetReview(thisChangeId, "current", &gerrit.ReviewInput{
		Message: reviewMessage,
	})
	if err != nil {
		return makeErr("failed to publish comment to gerrit", err)
	}

	if csstate == nil {
		csstate, err = GetChangesetState(owner, repo, prnum)
		if err != nil {
			return makeErr("failed to retrieve updated change from gerrit", err)
		}
		if csstate == nil {
			return makeErr("could not locate pushed change on gerrit", err)
		}
	}

	err = SendPushedText(owner, repo, prnum, prstate, csstate.ChangeNum)
	if err != nil {
		return err
	}

	return nil
}

func ProcessPullRequest(owner, repo string, prnum int) error {
	state, err := GetPullRequestState(owner, repo, prnum)
	if err != nil {
		return err
	}

	if state.CurrentState == BOTSTATE_ABANDONED || state.CurrentState == BOTSTATE_TIMEOUT ||
		state.CurrentState == BOTSTATE_MERGED {
		// That's odd... This ticket should not even be open...
		// Let's do nothing in case someone intentionally reopened it.
		return nil
	}

	if state.CurrentState == BOTSTATE_NEW || state.CurrentState == BOTSTATE_NO_CLA ||
		state.CurrentState == BOTSTATE_CREATED || state.CurrentState == BOTSTATE_UPDATED {
		// Check CLA
		allSigned, err := VerifyPrAuthorClas(owner, repo, prnum)
		if err != nil {
			return err
		}

		if !allSigned {
			if state.CurrentState == BOTSTATE_NO_CLA {
				// If we already sent the no_cla message, lets not do it again,
				//  instead we should check if this is now timed out...

				if time.Now().After(state.LastUpdatedTime.Add(10 * 24 * time.Hour)) {
					return ClosePrForTimeout(owner, repo, prnum, state)
				}

				log.Printf("Skipping this pull request as no_cla was already sent.")
				return nil
			}

			return SendClaText(owner, repo, prnum, state)
		} else {
			// Need to do normal process
			return TransferPrToGerrit(owner, repo, prnum, state)
		}
	}

	return makeErr("unexpected pull request state", nil)
}

func ProcessProject(owner, repo string) error {
	log.Printf("Processing project %s/%s", owner, repo)

	prs, _, err := githubClient.PullRequests.List(owner, repo, &github.PullRequestListOptions{
		State: "open",
	})
	if err != nil {
		return makeErr("failed to list all pull requests", err)
	}

	for i := 0; i < len(prs); i++ {
		prNum := *prs[i].Number
		log.Printf("Processing pull request %d", prNum)

		err := ProcessPullRequest(owner, repo, prNum)
		if err != nil {
			return err
		}
	}

	return nil
}

func ProcessAllProjects() error {
	log.Printf("Processing all projects")

	for i := 0; i < len(allRepos); i++ {
		thisRepo := allRepos[i]

		err := ProcessProject(thisRepo.Owner, thisRepo.Name)
		if err != nil {
			return err
		}
	}

	return nil
}

func initClients() error {
	_, err := os.Stat(gerritPrivateKey)
	if err != nil {
		return makeErr("failed to locate gerrit private key", err)
	}
	_, err = os.Stat(gerritPublicKey)
	if err != nil {
		return makeErr("failed to locate gerrit public key", err)
	}

	err = initGerritClient()
	if err != nil {
		return err
	}

	err = initGitHubClient()
	if err != nil {
		return err
	}

	return nil
}

func readConfig() error {
	configBytes, err := ioutil.ReadFile("./config.json")
	if err != nil {
		return makeErr("failed to read config file at `./config.json`", err)
	}

	var configData struct {
		DryRun bool
		GitHub struct {
			User   string
			Token  string
			Owners []string
		}
		Gerrit struct {
			Host string
			User string
			Pass string
			Keys struct {
				Public  string
				Private string
			}
			ClaGroupName string
		}
		Repos []struct {
			Owner string
			Name  string
			Repo  string
		}
	}
	err = json.Unmarshal(configBytes, &configData)
	if err != nil {
		return makeErr("failed to parse config file", err)
	}

	isDryRun = configData.DryRun
	botOwners = configData.GitHub.Owners
	githubUser = configData.GitHub.User
	githubToken = configData.GitHub.Token
	gerritHost = configData.Gerrit.Host
	gerritUser = configData.Gerrit.User
	gerritPass = configData.Gerrit.Pass
	gerritPublicKey = configData.Gerrit.Keys.Public
	gerritPrivateKey = configData.Gerrit.Keys.Private
	gerritClaGroupName = configData.Gerrit.ClaGroupName

	allRepos = nil
	for i := 0; i < len(configData.Repos); i++ {
		allRepos = append(allRepos, RepoInfo{
			Owner: configData.Repos[i].Owner,
			Name:  configData.Repos[i].Name,
			Repo:  configData.Repos[i].Repo,
		})
	}

	return nil
}

func githubHttpHandler(w http.ResponseWriter, r *http.Request) {
	log.Printf("Received GitHub webhook")

	var data github.WebHookPayload
	decoder := json.NewDecoder(r.Body)
	err := decoder.Decode(&data)

	if err != nil {
		log.Printf("Failed to parse GitHub data %+v", err)
		return
	}

	fmt.Fprintf(w, "success")

	if data.Repo == nil || data.Repo.Owner == nil {
		// No repository data in the webhook
		return
	}

	if data.Sender != nil && IsGitHubUserBot(data.Sender) {
		// Ignore hooks triggered by the bot itself.
		return
	}

	ownerName := *data.Repo.Owner.Login
	repoName := *data.Repo.Name

	go func() {
		err := ProcessProject(ownerName, repoName)
		if err != nil {
			log.Printf("githubHttpHandler error: %+v\n", err)
		}
	}()
}

func gerritHttpHandler(w http.ResponseWriter, r *http.Request) {
	log.Printf("Received Gerrit webhook")

	fmt.Fprintf(w, "success")

	go func() {
		err := ProcessAllProjects()
		if err != nil {
			log.Printf("gerritHttpHandler error: %+v\n", err)
		}
	}()
}

func rootHttpHandler(w http.ResponseWriter, r *http.Request) {
	fmt.Fprintf(w, "This is just a bot...")
}

func main() {
	log.Printf("Reading configuration...")

	err := readConfig()
	if err != nil {
		log.Printf("Failed to initalize configuration:")
		log.Printf("%+v", err)
		return
	}

	log.Printf("Initializing API clients...")

	err = initClients()
	if err != nil {
		log.Printf("Failed to initalize clients:")
		log.Printf("%+v", err)
		return
	}

	log.Printf("Starting web server on :4455...")

	http.HandleFunc("/", rootHttpHandler)
	http.HandleFunc("/github", githubHttpHandler)
	http.HandleFunc("/gerrit", gerritHttpHandler)
	err = http.ListenAndServe(":4455", nil)
	if err != nil {
		log.Printf("Failed to start http listening.")
		log.Printf("%+v", err)
		return
	}

	/*
		ownerName := "couchbase"
		repoName := "couchnode"
		prNum := 0

		if prNum > 0 {
			err = ProcessPullRequest(ownerName, repoName, prNum)
		} else {
			err = ProcessProject(ownerName, repoName)
		}

		if err != nil {
			log.Printf("An error occured during processing:")
			log.Printf("%+v", err)
		}
	*/
}
