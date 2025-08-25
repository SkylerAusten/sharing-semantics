#lang forge/temporal
open "file_sharing.frg"

// Pre-load the vizualization script
option run_sterling "viz.js"

-- Trace Length
option max_tracelength 8 -- Max Trace Length
option min_tracelength 4 -- Min Trace Length

-- UNSAT Resolver (uncomment to use)
// option solver MiniSatProver
// option core_minimization rce
// option logtranslation 1
// option coregranularity 1

// ------------------------------------------------------------
// Program-specific Sigs
// ------------------------------------------------------------
one sig Alice, Bob extends Person {}

one sig AliceDrive, BobDrive extends Drive {}

one sig AliceInbox, BobInbox extends Inbox {}

one sig AliceComputer, BobComputer extends Computer {}

// ------------------------------------------------------------
// Program-specific Properties
// ------------------------------------------------------------
pred ownership {
    AliceDrive in Drive implies {AliceDrive.location_owner = Alice}
    BobDrive in Drive implies {BobDrive.location_owner = Bob}

    AliceComputer in Computer implies {AliceComputer.location_owner = Alice}
    BobComputer in Computer implies {BobComputer.location_owner = Bob}

    AliceInbox in Inbox implies {AliceInbox.inbox_owner = Alice}
    BobInbox in Inbox implies {BobInbox.inbox_owner = Bob}
}

------------------------ Example States ------------------------

pred noItemsOrEmails {
    no Item
    no Email
    no EmailContent
}

pred aliceCreatedComputerFile {
	some f: File | {
		f.item_owner = Alice
		f.item_creator = Alice
		f.location = AliceComputer
		no f.shared_with
	}

    no Email
    no same_content
}

pred aliceUploadedFile {
	some disj f1, f2: File | {
		f1.item_owner = Alice
		f1.location = AliceComputer

		f2.item_owner = Alice
		f2.location = AliceDrive

		f2 in f1.same_content
	}

    no Email
}

pred aliceFileSharedWithBob {
	some f: File, l: Link, e: Email | {
		f.item_owner = Alice
		f.location = AliceDrive
		Bob in f.shared_with
		f in BobDrive.shared_with_me

		e in AliceInbox.sent
	}
}

pred twoFilesInFolder {
    some disj f1, f2: File, fold: Folder | {
        f1 in fold.folder_items
        f2 in fold.folder_items
    }
}

pred fileInBobDrive {
    some f: File | f in BobDrive.location_items

}

pred emailSentWithAttachment {
    some e: Email | {
        some e.to
        some e.from
        some e.email_content
        e.email_content in Attachment
        some f: Folder | {
            some f.folder_items
            e.email_content.attached = f
        }
    }

    some sent
}

pred someSharedFile {
    some shared_with_me
}

pred editsMade {
    eventually { some same_content and eventually { no same_content } }
}

--

pred allTransitions {
    always {
        doNothing or {
            some p: (Person - Server), l: Location | { createFile[p, l] }
        } or {
            some p: (Person - Server), l: Location | { createFolder[p, l] }
        } or {
            some p: Person, m: File, d: Folder | { moveItem[p, m, d] }
        } or {
            some p: Person | { createEmail[p] }
        } or {
            some p, r: Person, e: Email | { setRecipients[p, e, r] }
        } or {
            some p: Person, i: Item, e: Email | { addLink[p, i, e] }
        } or {
            some p: Person, e: Email | { sendEmail[p, e] }
        } or {
            some p: Person, a: File, e: Email | { attachFile[p, a, e] }
        } or {
            some p: Person, a: Folder, e: Email | { attachFolder[p, a, e] }
        } or {
            some p: Person, e: Email | { addText[p, e] }
        } or {
            some p: Person, f: File | { editFile[p, f] }
        } or {
            some p: Person, e, r: Email | sendReply[p, e, r]
        } or {
            some p: Person, e: Email | downloadFileAttachment[p, e]
        } or {
            some p: Person, f: File | { uploadFileToDrive[p, f] }
        } or {
            some p: Person, f: File | { downloadDriveFile[p, f] }
        } or {
            some p: Person, f: File | { duplicateFile[p, f] }
        }
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

pred shareItemTransitions {
    always {
        doNothing or {
            some p: (Person - Server), l: Location | { createFile[p, l] }
        } or {
            some p, r: Person, i: Item | { shareItem[p, i, r] }
        }
    }
}

------------------------ Run Statements ------------------------

pred initState {
    noItemsOrEmails
}

pred midStates {
    eventually { aliceCreatedComputerFile and eventually { aliceUploadedFile } }
}

pred finalState {
    aliceFileSharedWithBob
}

pred testTraces {
    initState
    modelProperties and ownership
    // next_state {not modelProperties}
    limitedTransitions
    eventually {midStates}
    eventually {always {finalState}}
}

run {
    testTraces
} for exactly 3 Person, -- Should be at least 3 to exercise full functionality (Sender, Server, Recipient).
    exactly 5 Location,
    exactly 2 Drive, -- MUST correspond to the # of Persons.
    exactly 2 Computer, -- MUST correspond to the # of Persons.
    exactly 1 EmailServer, -- MUST be exactly 1.
    exactly 2 Inbox, -- MUST correspond to the # of Persons.
    8 Item, 7 File, 1 Folder, -- # Files and # Folders should add up to # Items, but this isn't required.
    2 EmailContent, 2 Email -- These should be equal for all emails to be sendable, but this isn't required.