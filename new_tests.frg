#lang forge/temporal

open "file_sharing.frg"

option max_tracelength 12
option min_tracelength 8

// option solver MiniSatProver
// option core_minimization rce
// option logtranslation 1
// option coregranularity 1

------------------------ Model Constraint Tests ------------------------

-- Test that modelProperties is sat given specified Sig counts.
test expect { modelPropertiesSat: {modelProperties}
    for exactly 3 Person,
    exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
    exactly 1 EmailServer, exactly 2 Inbox,
    5 Item, 5 File, 2 Folder,
    3 EmailContent, 3 Email
is sat }

-- Test that an email being in both sent or received and drafts is UNSAT.
pred draftsAndSent {
    some e: Email, i: Inbox | {e in i.drafts and e in i.sent} or {e in i.drafts and e in i.received}
    some e: Email, i1, i2: Inbox | {e in i1.drafts and e in i2.sent} or {e in i1.drafts and e in i2.received}
}

test expect { draftsAndSentUnsat: {modelProperties and draftsAndSent}
    for exactly 3 Person,
    exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
    exactly 1 EmailServer, exactly 2 Inbox,
    5 Item, 5 File, 2 Folder,
    3 EmailContent, 3 Email
is unsat }

-- Test that a reflexive same_content is UNSAT.
pred cyclicalSameContent {
    some f: File | f in f.same_content
}

test expect { cyclicalSameContentUnsat: {modelProperties and cyclicalSameContent}
    for exactly 3 Person,
    exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
    exactly 1 EmailServer, exactly 2 Inbox,
    5 Item, 5 File, 2 Folder,
    3 EmailContent, 3 Email
is unsat }

-- Test that a non-symmetric same_content is UNSAT.
pred nonSymmetricSameContent {
    some disj f1, f2: File | {
        f1 in f2.same_content
        f2 not in f1.same_content
    }
}

test expect { nonSymmetricSameContentUnsat: {modelProperties and nonSymmetricSameContent}
    for exactly 3 Person,
    exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
    exactly 1 EmailServer, exactly 2 Inbox,
    5 Item, 5 File, 2 Folder,
    3 EmailContent, 3 Email
is unsat }

-- Test that a non-transitive same_content is UNSAT.
pred nonTransitiveSameContent {
    some disj f1, f2, f3: File | {
        f1 in f2.same_content
        f2 in f3.same_content
        f1 not in f3.same_content
    }
}

test expect { nonTransitiveSameContentUnsat: {modelProperties and nonSymmetricSameContent}
    for exactly 3 Person,
    exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
    exactly 1 EmailServer, exactly 2 Inbox,
    5 Item, 5 File, 2 Folder,
    3 EmailContent, 3 Email
is unsat }

-- Check transitive closure pred equivalences.
pred transitiveClosure1 {
    all disj f1, f2: File |
        f2 in f1.^same_content implies f2 in f1.same_content
}

pred transitiveClosure2 {
    all disj f1, f2, f3: File |
        (f1 in f2.same_content and f2 in f3.same_content) implies f1 in f3.same_content
}

assert transitiveClosure1 is sufficient for transitiveClosure2
    for exactly 3 Person,
    exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
    exactly 1 EmailServer, exactly 2 Inbox,
    5 Item, 5 File, 2 Folder,
    3 EmailContent, 3 Email

assert transitiveClosure1 is necessary for transitiveClosure2
    for exactly 3 Person,
    exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
    exactly 1 EmailServer, exactly 2 Inbox,
    5 Item, 5 File, 2 Folder,
    3 EmailContent, 3 Email

assert transitiveClosure2 is sufficient for transitiveClosure1
    for exactly 3 Person,
    exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
    exactly 1 EmailServer, exactly 2 Inbox,
    5 Item, 5 File, 2 Folder,
    3 EmailContent, 3 Email

assert transitiveClosure2 is necessary for transitiveClosure1
    for exactly 3 Person,
    exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
    exactly 1 EmailServer, exactly 2 Inbox,
    5 Item, 5 File, 2 Folder,
    3 EmailContent, 3 Email







    // -- An email in an inbox's drafts implies the email is "from" the inbox owner.
    // all e: Email, i: Inbox | {e in i.drafts implies e.from = i.inbox_owner}

    // -- An email in an inbox's sent implies the email is "from" the inbox owner.
    // all e: Email, i: Inbox | {e in i.sent implies e.from = i.inbox_owner}

    // -- A file cannot have the same content as itself.
    // no f: File | f in f.same_content

    // -- All items specified as being at a given location will be in that location's location_items set.
    // all l: Location, i: Item | i in l.location_items iff {i.location = l}

    // -- A item must be in a drive to be shared with someone.
    // all i: Item | some i.shared_with implies {i.location in Drive}

    // -- An item cannot be shared with its owner.
    // no i: Item | i.item_owner in i.shared_with

    // -- No file can be both in someone's drive & that drive's shared_with_me.
    // no i: Item, d: Drive | i in d.location_items and i in d.shared_with_me

    // -- An item's location must have the same location_owner as the item's item_owner.
    // all f: Item | f.location.location_owner = f.item_owner

    // -- All items must have the same location as the folder they're in.
    // all file: File, folder: Folder | file in folder.folder_items implies file.location = folder.location

    // -- All same_content relations are symmetric.
    // all disj f1, f2: File | f2 in f1.same_content iff { f1 in f2.same_content }

    // // -- same_content is transitively closed.
    // // all disj f1, f2: File |
	// // 	f2 in f1.^same_content implies f2 in f1.same_content

    // all disj f1, f2, f3: File | (f1 in f2.same_content and f2 in f3.same_content) implies f1 in f3.same_content

    // -- No item can be in more than one folder's items.
    // no disj f1, f2: Folder, i: Item |
    //     (i in f1.folder_items) and (i in f2.folder_items)

    // -- No item can be in more than one location's location_items.
    // no disj l1, l2: Location, i: Item |
    //     (i in l1.location_items) and (i in l2.location_items)

    // -- An foler cannot be in its own folder_items or any child folders's items.
    // no f: Folder | f in f.^folder_items

    // -- One person can only own one computer, one drive, and one inbox.
    // -- And all computers, drives, and inboxes must be owned.
    // #{Computer.location_owner} = #{Computer}
    // #{Drive.location_owner} = #{Drive}
    // #{Inbox.inbox_owner} = #{Inbox}

    // -- No two emails can have the same content.
    // no disj e1, e2: Email | {e1.email_content = e2.email_content and {e1.email_content + e2.email_content} != none }

    // -- A item must be in a drive to be in another drive's shared_with_me.
    // all i: Item | { i in Drive.shared_with_me implies {i.location in Drive}}

    // -- An item shared with someone must be in that person's drive's shared_with_me.
    // all i: Item, p: Person | {p in i.shared_with iff {i in ((location_owner.p) & Drive).shared_with_me}}

    // -- An item NOT shared with someone must NOT be in that person's drive's shared_with_me.
    // all i: Item, p: Person | {p not in i.shared_with implies {i not in ((location_owner.p) & Drive).shared_with_me}}

    // -- An item in a folder must inherit the folder's shared_with.
    // no file: File, folder: Folder | file in folder.folder_items and folder.shared_with not in file.shared_with

    // -- The email server must be owned by the Server person.
    // EmailServer in Location implies {EmailServer.location_owner = Server}

    // -- An attached item must be on the email server.
    // all a: Attachment | a.attached.location = EmailServer

    // -- A linked item must be in a Drive.
    // all l: Link | l.points_to.location in Drive

    // -- An email in sent or received must have some content & some "to."
    // all e: Email, i: Inbox | (e in i.sent or e in i.received) implies some e.email_content and some e.to

    // -- All email content must have some associated email.
    // all ec: EmailContent | some e: Email | e.email_content = ec

    // -- Server cannot own a Drive, Computer, or Inbox.
    // no d: Drive | d.location_owner = Server
    // no c: Computer | c.location_owner = Server
    // no i: Inbox | i.inbox_owner = Server

    // -- Every email must have some "from".
    // all e: Email | some e.from

    // -- An email in drafts cannot be in any inbox's sent or received.
    // all disj i1, i2: Inbox, e: Email | e in i1.drafts implies {
    //     e not in (i2.sent + i2.received + i1.sent + i1.received + i2.drafts)
    // }