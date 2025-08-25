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
// Program-specific Goal States
// ------------------------------------------------------------

// No items or emails in the initial state.
pred noItemsOrEmails {
    no Item
    no Email
    no EmailContent
}

pred aliceCreatedDriveFile {
	some f: File | {
		f.item_owner = Alice
		f.item_creator = Alice
		f.location = AliceDrive
		no f.shared_with
	}

    no Email
    no same_content
}

pred aliceFileSharedWithJoe {
	some f: File, l: Link, e: Email | {
		f.item_owner = Alice
		f.location = AliceDrive
		Joe in f.shared_with
		f in JoeDrive.shared_with_me

		e in AliceInbox.sent
		e.from = Alice
		e.to = Joe
		e.email_content = l
		l.points_to = f
	}
}

pred limitedTransitions {
    always {
        doNothing or {
            some p: (Person - Server), l: Location | { createFile[p, l] }
        } or {
            some p: Person | { createEmail[p] }
        } or {
            some p, r: Person, e: Email | { setRecipients[p, e, r] }
        } or {
            some p: Person, i: Item, e: Email | { addLink[p, i, e] }
        } or {
            some p: Person, e: Email | { sendEmail[p, e] }
        } or {
            some p: Person, f: File | { uploadFileToDrive[p, f] }
        }
    }
}

------------------------ Run Statements ------------------------

pred initState {
    noItemsOrEmails
}

pred midStates {
    eventually {aliceCreatedDriveFile}
}

pred finalState {
    aliceFileSharedWithJoe
}

pred traceProperties {
    #{File} <= 1
}

pred menuTraces {
    initState
    modelProperties and ownership
    limitedTransitions
    always {traceProperties}
    eventually {midStates}
    eventually {always {finalState}}
}

run {
    menuTraces
} for exactly 3 Person, -- Should be at least 3 to exercise full functionality (Sender, Server, Recipient).
    exactly 5 Location,
    exactly 2 Drive, -- MUST correspond to the # of Persons.
    exactly 2 Computer, -- MUST correspond to the # of Persons.
    exactly 1 EmailServer, -- MUST be exactly 1.
    exactly 2 Inbox, -- MUST correspond to the # of Persons.
    8 Item, 7 File, 1 Folder, -- # Files and # Folders should add up to # Items, but this isn't required.
    2 EmailContent, 2 Email -- These should be equal for all emails to be sendable, but this isn't required.