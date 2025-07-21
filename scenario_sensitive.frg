#lang forge/temporal
open "file_sharing.frg"

option max_tracelength 13
option min_tracelength 12

// option solver MiniSatProver
// option core_minimization rce
// option logtranslation 1
// option coregranularity 1

// ------------------------------------------------------------
// Program-specific Sigs
// ------------------------------------------------------------
one sig David, Erica extends Person {}

one sig DavidDrive, EricaDrive extends Drive {}

one sig DavidInbox, EricaInbox extends Inbox {}

one sig DavidComputer, EricaComputer extends Computer {}

// ------------------------------------------------------------
// Program-specific Properties
// ------------------------------------------------------------
pred ownership {
    DavidDrive in Drive implies {DavidDrive.location_owner = David}
    EricaDrive in Drive implies {EricaDrive.location_owner = Erica}

    DavidComputer in Computer implies {DavidComputer.location_owner = David}
    EricaComputer in Computer implies {EricaComputer.location_owner = Erica}

    DavidInbox in Inbox implies {DavidInbox.inbox_owner = David}
    EricaInbox in Inbox implies {EricaInbox.inbox_owner = Erica}
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

// After David creates the local file on his computer.
pred davidCreatedLocalFile {
    some f: File | {
        f.item_owner = David
        f.location = DavidComputer
    }
}

// After David emails it to Erica & she Downloads.
pred davidEmailsToErica{
    some disj f, s, e: File, em: Email | {
        f.item_owner = David
        f.location = DavidComputer

        s.item_owner = Server
        s.location = EmailServer

        e.item_owner = Erica
        e.location = EricaComputer

        f in s.same_content
        s in e.same_content

        em.from = David
        em.to = Erica

        em in DavidInbox.sent
    }   

    #{Email} = 1
    #{File} = 3

}

// After Erica edits her copy.
pred ericaEdits {
    some disj f, s, e: File, em: Email | {
        f.item_owner = David
        f.location = DavidComputer

        s.item_owner = Server
        s.location = EmailServer

        e.item_owner = Erica
        e.location = EricaComputer

        f in s.same_content
        no e.same_content

        em.from = David
        em.to = Erica

        em in EricaInbox.sent
    }
}

pred ericaSendsBack {
    some disj f1, s1, e, s2, f2: File, em1, em2: Email | {
        f1.item_owner = David
        f1.location = DavidComputer

        s1.item_owner = Server
        s1.location = EmailServer

        e.item_owner = Erica
        e.location = EricaComputer

        s2.item_owner = Server
        s2.location = EmailServer

        f2.item_owner = David
        f2.location = DavidComputer

        f1 in s1.same_content
        s1 not in e.same_content
        e in f2.same_content
        s2 in f2.same_content
        f1 not in f2.same_content

        em1.from = David
        em1.to = Erica

        em2.from = Erica
        em2.to = David

        em1 in DavidInbox.sent
        em2 in EricaInbox.sent
    }   
}

pred midStatesSensitive {
    eventually {
        davidCreatedLocalFile
      and eventually {
        davidEmailsToErica
    //   and eventually {
    //     // ericaEdits
    //     // }
        }
    }
}

pred finalStateSensitive {
    ericaSendsBack
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

pred sensitiveTraces {
    startState
    modelProperties and ownership
    limitedTransitions

    eventually { midStatesSensitive }
    eventually { always { finalStateSensitive } }
}

run {
    sensitiveTraces
} for exactly 3 Person, -- Should be at least 3 to exercise full functionality (Sender, Server, Recipient).
    exactly 5 Location,
    exactly 2 Drive, -- MUST correspond to the # of Persons.
    exactly 2 Computer, -- MUST correspond to the # of Persons.
    exactly 1 EmailServer, -- MUST be exactly 1.
    exactly 2 Inbox, -- MUST correspond to the # of Persons.
    5 Item, 5 File, 0 Folder, -- # Files and # Folders should add up to # Items, but this isn't required.
    2 EmailContent, 2 Email -- These should be equal for all emails to be sendable, but this isn't required.