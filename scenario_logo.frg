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
one sig Frank, Kate extends Person {}

one sig FrankDrive, KateDrive extends Drive {}

one sig FrankInbox, KateInbox extends Inbox {}

one sig FrankComputer, KateComputer extends Computer {}

// ------------------------------------------------------------
// Program-specific Properties
// ------------------------------------------------------------
pred ownership {
    FrankDrive in Drive implies {FrankDrive.location_owner = Frank}
    KateDrive in Drive implies {KateDrive.location_owner = Kate}

    FrankComputer in Computer implies {FrankComputer.location_owner = Frank}
    KateComputer in Computer implies {KateComputer.location_owner = Kate}

    FrankInbox in Inbox implies {FrankInbox.inbox_owner = Frank}
    KateInbox in Inbox implies {KateInbox.inbox_owner = Kate}
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

// After Frank creates the local file on his computer.
pred frankCreatedLocalFile {
    some f: File | {
        f.item_owner = Frank
        f.location = FrankComputer
    }
    no Email

    no k: File | {
        k.item_owner = Kate
        k.location = KateComputer
    }
}

// After Frank emails it to Kate.
pred frankEmailedToKate{
    some disj f, s: File, a: Attachment, e: Email | {
        s.item_owner = Server
        s.location = EmailServer

        f.item_owner = Frank
        f.location = FrankComputer

        f in s.same_content
        s in f.same_content

        e in FrankInbox.sent
        e.from = Frank
        e.to = Kate
        e.email_content = a
        a.attached = s
    }

    no k: File | {
        k.item_owner = Kate
        k.location = KateComputer
    }
}

// After Frank download locally.
pred kateDownloaded {
    some disj f, k, s: File | {
        f.item_owner = Frank
        f.location  = FrankComputer

        k.item_owner = Kate
        k.location   = KateComputer

        s.item_owner = Server
        s.location   = EmailServer

        f in s.same_content
        s in k.same_content
    }
}

pred kateEditsMade {
    some disj f, k, s: File | {
        f.item_owner = Frank
        f.location  = FrankComputer

        k.item_owner = Kate
        k.location   = KateComputer

        s.item_owner = Server
        s.location   = EmailServer

        no k.same_content
        f in s.same_content
        s in f.same_content
    }
}

pred frankEditsMade {
    some disj f, k, s: File | {
        f.item_owner = Frank
        f.location  = FrankComputer

        k.item_owner = Kate
        k.location   = KateComputer

        s.item_owner = Server
        s.location   = EmailServer

        no same_content
    }
}

pred midStatesLogo {
    eventually {
        frankCreatedLocalFile
      and eventually {
        frankEmailedToKate
      and eventually {
        kateDownloaded
      and eventually {
        kateEditsMade
      }}}
    }
}

pred finalStateLogo {
    frankEditsMade
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
            some p: Person, e: Email | { downloadFileAttachment[p, e] }
        } or {
            some p: Person, f: File | { editFile[p, f] }
        }
    }
}

------------------------ Run Statements ------------------------

pred logoTraces {
    startState
    modelProperties and ownership
    limitedTransitions

    eventually { midStatesLogo }
    eventually { always { finalStateLogo } }
}

run {
    logoTraces
} for exactly 3 Person, -- Should be at least 3 to exercise full functionality (Sender, Server, Recipient).
    exactly 5 Location,
    exactly 2 Drive, -- MUST correspond to the # of Persons.
    exactly 2 Computer, -- MUST correspond to the # of Persons.
    exactly 1 EmailServer, -- MUST be exactly 1.
    exactly 2 Inbox, -- MUST correspond to the # of Persons.
    3 Item, 3 File, 0 Folder, -- # Files and # Folders should add up to # Items, but this isn't required.
    2 EmailContent, 2 Email -- These should be equal for all emails to be sendable, but this isn't required.