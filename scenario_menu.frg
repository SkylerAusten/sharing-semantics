#lang forge/temporal
open "file_sharing.frg"

option max_tracelength 12
option min_tracelength 8

// option solver MiniSatProver
// option core_minimization rce
// option logtranslation 1
// option coregranularity 1

// ------------------------------------------------------------
// Program-specific Sigs
// ------------------------------------------------------------
one sig Alice, Joe extends Person {}

one sig AliceDrive, JoeDrive extends Drive {}

one sig AliceInbox, JoeInbox extends Inbox {}

one sig AliceComputer, JoeComputer extends Computer {}

// ------------------------------------------------------------
// Program-specific Properties
// ------------------------------------------------------------
pred ownership {
    AliceDrive in Drive implies {AliceDrive.location_owner = Alice}
    JoeDrive in Drive implies {JoeDrive.location_owner = Joe}

    AliceComputer in Computer implies {AliceComputer.location_owner = Alice}
    JoeComputer in Computer implies {JoeComputer.location_owner = Joe}

    AliceInbox in Inbox implies {AliceInbox.inbox_owner = Alice}
    JoeInbox in Inbox implies {JoeInbox.inbox_owner = Joe}
}

// ------------------------------------------------------------
// Paper Goal Program
// ------------------------------------------------------------
// createFile[Alice, AliceDrive] // Alice creates a menu with Burgers in her Google Drive.
//

// - Alice creates menu with burgers in Google Docs.
// - Alice gives Joe share access.
// - Alice creates email.
// - Alice adds Joe as recipient.
// - Alice adds link to email body.
// - Alice sends e-mail.
// - Joe edits menu to be a list of salads.

// ------------------------------------------------------------
// Program-specific Goal States
// ------------------------------------------------------------

// No items or emails in the initial state.
pred startState {
    no Item
    no Email
    no EmailContent
}