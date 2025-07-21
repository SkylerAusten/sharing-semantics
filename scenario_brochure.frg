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
one sig Olivia, Charlie extends Person {}

one sig OliviaDrive, CharlieDrive extends Drive {}

one sig OliviaInbox, CharlieInbox extends Inbox {}

one sig OliviaComputer, CharlieComputer extends Computer {}

// ------------------------------------------------------------
// Program-specific Properties
// ------------------------------------------------------------
pred ownership {
    OliviaDrive in Drive implies {OliviaDrive.location_owner = Olivia}
    CharlieDrive in Drive implies {CharlieDrive.location_owner = Charlie}

    OliviaComputer in Computer implies {OliviaComputer.location_owner = Olivia}
    CharlieComputer in Computer implies {CharlieComputer.location_owner = Charlie}

    OliviaInbox in Inbox implies {OliviaInbox.inbox_owner = Olivia}
    CharlieInbox in Inbox implies {CharlieInbox.inbox_owner = Charlie}
}

// ------------------------------------------------------------
// Program-specific Goal States
// ------------------------------------------------------------

// No items or emails in the initial state.
pred startState {
    no Item
    no Email
    no EmailContent
}

// After Olivia creates the local file on her computer.
pred oliviaCreatedLocalFile {
    some o: File | {
        o.item_owner = Olivia
        o.location = OliviaComputer
    }
    no Email

    no c: File | {
        c.item_owner = Charlie
        c.location = CharlieComputer
    }
}

// After Olivia uploads her file to Drive.
pred oliviaUploadsToDrive{
    some disj ol, od: File | {
        ol.item_owner = Olivia
        ol.location = OliviaComputer

        od.item_owner = Olivia
        od.location = OliviaDrive

        ol.same_content = od
        od.same_content = ol
    }

    no c: File | {
        c.item_owner = Charlie
        c.location = CharlieComputer
    }
}

// After Olivia shares it with Charlie.
pred shareWithCharlie {
    some od: File | {
        od.item_owner = Olivia
        od.location  = OliviaDrive

        od.shared_with = Charlie
        CharlieDrive.shared_with_me = od
    }
}

pred charlieEditsMade {
    no same_content
}

pred midStatesBrochure {
    eventually {
        oliviaCreatedLocalFile
      and eventually {
        oliviaUploadsToDrive
      and eventually {
        shareWithCharlie
        }}
    }
}

pred finalStateBrochure {
    charlieEditsMade
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
            some p: Person, i: File, e: Email | { attachFile[p, i, e] }
        } or {
            some p: Person, e: Email | { sendEmail[p, e] }
        } or {
            some p: Person, f: File | { uploadFileToDrive[p, f] }
        } or {
            some disj p, t: Person, f: Item | { shareItem[p, f, t] }
        } or {
            some p: Person, f: File | { editFile[p, f] }
        }
    }
}

------------------------ Run Statements ------------------------

pred brochureTraces {
    startState
    modelProperties and ownership
    limitedTransitions

    eventually { midStatesBrochure }
    eventually { always { finalStateBrochure } }
}

run {
    brochureTraces
} for exactly 3 Person, -- Should be at least 3 to exercise full functionality (Sender, Server, Recipient).
    exactly 5 Location,
    exactly 2 Drive, -- MUST correspond to the # of Persons.
    exactly 2 Computer, -- MUST correspond to the # of Persons.
    exactly 1 EmailServer, -- MUST be exactly 1.
    exactly 2 Inbox, -- MUST correspond to the # of Persons.
    2 Item, 2 File, 0 Folder, -- # Files and # Folders should add up to # Items, but this isn't required.
    2 EmailContent, 2 Email -- These should be equal for all emails to be sendable, but this isn't required.