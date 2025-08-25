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
one sig Aaron, Marie extends Person {}

one sig AaronDrive, MarieDrive extends Drive {}

one sig AaronInbox, MarieInbox extends Inbox {}

one sig AaronComputer, MarieComputer extends Computer {}

// ------------------------------------------------------------
// Program-specific Properties
// ------------------------------------------------------------
pred ownership {
    AaronDrive in Drive implies {AaronDrive.location_owner = Aaron}
    MarieDrive in Drive implies {MarieDrive.location_owner = Marie}

    AaronComputer in Computer implies {AaronComputer.location_owner = Aaron}
    MarieComputer in Computer implies {MarieComputer.location_owner = Marie}

    AaronInbox in Inbox implies {AaronInbox.inbox_owner = Aaron}
    MarieInbox in Inbox implies {MarieInbox.inbox_owner = Marie}
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

// After Marie creates the online doc in her Drive.
pred marieCreatedDriveFile {
    some f: File | {
        f.item_owner = Marie
        f.location = MarieDrive
        no f.shared_with
    }
    no Email
}

// After she shares it with Aaron.
pred marieSharedWithAaron {
    some f: File, l: Link, e: Email | {
        f.item_owner = Marie
        f.location = MarieDrive
        f.shared_with = Aaron
        AaronDrive.shared_with_me = f

        e in MarieInbox.sent
        e.from = Marie
        e.to = Aaron
        e.email_content = l
        l.points_to = f
    }
}

// After Aaron download locally.
pred aaronDownloaded {
    some disj f, g: File | {
        g.item_owner = Aaron
        g.location  = AaronComputer
        no g.shared_with
        g in f.same_content

        f in g.same_content
        f.item_owner = Marie
        f.location   = MarieDrive
        Aaron in f.shared_with
    }
}

pred editsMade {
    some disj f, g: File | {
        g.item_owner = Aaron
        g.location  = AaronComputer
        no g.shared_with
        g not in f.same_content

        f not in g.same_content
        f.item_owner = Marie
        f.location   = MarieDrive
        Aaron in f.shared_with
    }
}

pred midStatesFarm {
    eventually {
        marieCreatedDriveFile
      and eventually {
        marieSharedWithAaron
      and eventually {
        aaronDownloaded
      }}
    }
}

pred finalStateFarm {
    editsMade
}

pred traceProperties {
    #{File} <= 2
}

pred limitedTransitions {
    always {
        doNothing or {
            some p: (Person - Server), l: Location | { createFile[p, l] }
        } or {
            some p, t: Person, i: Item | { shareItem[p, i, t] }
        } or {
            some p: Person, f: File | { downloadDriveFile[p, f] }
        } or {
            some p: Person, f: File | { editFile[p, f] }
        }
    }
}

------------------------ Run Statements ------------------------

pred farmTraces {
    startState
    modelProperties and ownership
    limitedTransitions
    always {traceProperties}
    eventually { midStatesFarm }
    eventually { always { finalStateFarm } }
}

run {
    farmTraces
} for exactly 3 Person, -- Should be at least 3 to exercise full functionality (Sender, Server, Recipient).
    exactly 5 Location,
    exactly 2 Drive, -- MUST correspond to the # of Persons.
    exactly 2 Computer, -- MUST correspond to the # of Persons.
    exactly 1 EmailServer, -- MUST be exactly 1.
    exactly 2 Inbox, -- MUST correspond to the # of Persons.
    2 Item, 2 File, 0 Folder, -- # Files and # Folders should add up to # Items, but this isn't required.
    2 EmailContent, 2 Email -- These should be equal for all emails to be sendable, but this isn't required.