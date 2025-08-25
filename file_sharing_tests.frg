#lang forge/temporal

open "file_sharing.frg"

option max_tracelength 12
option min_tracelength 1

-- Options to help with UNSAT core resolution:
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


-- Test that a file in a location_items other than its own location is UNSAT.
pred itemInTwoLocations {
    some disj l1, l2: Location, i: Item | i.location = l1 and i in l2.location_items
}

test expect { itemInTwoLocationsUnsat: {modelProperties and itemInTwoLocations}
    for exactly 3 Person,
    exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
    exactly 1 EmailServer, exactly 2 Inbox,
    5 Item, 5 File, 2 Folder,
    3 EmailContent, 3 Email
is unsat }

-- Test that a file being on a computer and being shared with someone is UNSAT.
pred sharedComputerItem {
    some i: Item | i.location in Computer and some i.shared_with or {
        some i: Item | i.location in Computer and i in Drive.shared_with_me
    }
}

test expect { sharedComputerItemUnsat: {modelProperties and sharedComputerItem}
    for exactly 3 Person,
    exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
    exactly 1 EmailServer, exactly 2 Inbox,
    5 Item, 5 File, 2 Folder,
    3 EmailContent, 3 Email
is unsat }

-- Test that an item cannot be shared with its owner.
pred itemSharedWithOwner {
    some i: Item | i.item_owner in i.shared_with
}

test expect { itemSharedWithOwnerUnsat: {modelProperties and itemSharedWithOwner}
    for exactly 3 Person,
    exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
    exactly 1 EmailServer, exactly 2 Inbox,
    5 Item, 5 File, 2 Folder,
    3 EmailContent, 3 Email
is unsat }

-- Test that an item's location must have the same location_owner as the item's item_owner.
pred mismatchedItemLocationOwner {
    some i: Item | i.location.location_owner != i.item_owner
}

test expect { mismatchedItemLocationOwnerUnsat: {modelProperties and mismatchedItemLocationOwner}
    for exactly 3 Person,
    exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
    exactly 1 EmailServer, exactly 2 Inbox,
    5 Item, 5 File, 2 Folder,
    3 EmailContent, 3 Email
is unsat }

-- All same_content relations are reciprocal.
pred nonReciprocalSameContent {
    some disj f1, f2: File | f2 in f1.same_content and not (f1 in f2.same_content)
}

test expect { nonReciprocalSameContentUnsat: {modelProperties and nonReciprocalSameContent}
    for exactly 3 Person,
    exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
    exactly 1 EmailServer, exactly 2 Inbox,
    5 Item, 5 File, 2 Folder,
    3 EmailContent, 3 Email
is unsat }

-- Two transitions cannot be taken in one step.
pred twoTransitionsOneStep {
  some p: Person - Server, l: Location, f: File, folder: Folder, e: Email, r: Person, i: Item |
    (createFile[p, l] and createEmail[p]) or
    (createFile[p, l] and moveItem[p, f, folder]) or
    (moveItem[p, f, folder] and setRecipients[p, e, r]) or
    (createEmail[p] and addLink[p, i, e]) or
    (sendEmail[p, e] and duplicateFile[p, f])
    -- Add other pairs of transitions.
}

test expect {
  noTwoTransitionsSameStep: {modelProperties and twoTransitionsOneStep}
  for exactly 3 Person,
      exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
      exactly 1 EmailServer, exactly 2 Inbox,
      5 Item, 5 File, 2 Folder,
      3 EmailContent, 3 Email
  is unsat
}

-- Test that two emails cannot have the same content.
pred duplicateEmailContent {
    some disj e1, e2: Email | some e1.email_content and some e2.email_content and {e1.email_content = e2.email_content}
}

test expect {
  duplicateEmailContentUnsat: {modelProperties and duplicateEmailContent}
  for exactly 3 Person,
      exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
      exactly 1 EmailServer, exactly 2 Inbox,
      5 Item, 5 File, 2 Folder,
      3 EmailContent, 3 Email
  is unsat
}

-- Test that Server cannot be a sender or recipient of an email.
pred serverSenderOrRecipient {
    some e: Email | {e.from = Server or e.to = Server}
}

test expect {
  serverSenderOrRecipientUnsat: {modelProperties and serverSenderOrRecipient}
  for exactly 3 Person,
      exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
      exactly 1 EmailServer, exactly 2 Inbox,
      5 Item, 5 File, 2 Folder,
      3 EmailContent, 3 Email
  is unsat
}

-- Test that a linked item must be in a Drive.
pred linkedItemNotInDrive {
    some l: Link | l.points_to.location not in Drive or {
        (some l.points_to.folder_items and l.points_to.^folder_items.location not in Drive)
    }
}

test expect {
  linkedItemNotInDriveUnsat: {modelProperties and linkedItemNotInDrive}
  for exactly 3 Person,
      exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
      exactly 1 EmailServer, exactly 2 Inbox,
      5 Item, 5 File, 2 Folder,
      3 EmailContent, 3 Email
  is unsat
}

-- Test that an email in drafts cannot be in any inbox's sent or received.
pred emailInDraftsAndSentOrReceived {
    some disj i1, i2: Inbox, e: Email | e in i1.drafts and (e in i2.sent or e in i2.received or e in i1.sent or e in i1.received)
}

test expect {
  emailInDraftsAndSentOrReceivedUnsat: {modelProperties and emailInDraftsAndSentOrReceived}
  for exactly 3 Person,
      exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
      exactly 1 EmailServer, exactly 2 Inbox,
      5 Item, 5 File, 2 Folder,
      3 EmailContent, 3 Email
  is unsat
}

-- Test that Server cannot own a Drive, Computer, or Inbox.
pred serverOwnsProhibitedLocations {
    some d: Drive | d.location_owner = Server or {
        some c: Computer | c.location_owner = Server
    } or {
        some i: Inbox | i.inbox_owner = Server
    }
}

test expect {
  serverOwnsProhibitedLocationsUnsat: {modelProperties and serverOwnsProhibitedLocations}
  for exactly 3 Person,
      exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
      exactly 1 EmailServer, exactly 2 Inbox,
      5 Item, 5 File, 2 Folder,
      3 EmailContent, 3 Email
  is unsat
}

-- Test that all items in folders must have the same location as the folder.
pred itemFolderLocationMismatch {
    some file: File, folder: Folder | file in folder.folder_items and file.location != folder.location
}

test expect {
  itemFolderLocationMismatchUnsat: {modelProperties and itemFolderLocationMismatch}
  for exactly 3 Person,
      exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
      exactly 1 EmailServer, exactly 2 Inbox,
      5 Item, 5 File, 2 Folder,
      3 EmailContent, 3 Email
  is unsat
}

-- Test the sharing bijection for shared_with_me.
pred shareImplies {
    -- An item shared with someone must be in that person's drive's shared_with_me.
    all i: Item, p: Person | {p in i.shared_with implies {i in ((location_owner.p) & Drive).shared_with_me}}

    -- An item NOT shared with someone must NOT be in that person's drive's shared_with_me.
    all i: Item, p: Person | {p not in i.shared_with implies {i not in ((location_owner.p) & Drive).shared_with_me}}
}

assert modelProperties is sufficient for shareImplies
  for exactly 3 Person,
      exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
      exactly 1 EmailServer, exactly 2 Inbox,
      5 Item, 5 File, 2 Folder,
      3 EmailContent, 3 Email

-- Test that doNothing cannot violate modelProperties or ownership or create new Items, Emails, or EmailContents.
pred doNothingTraces {
    {no Item and no Email and no EmailContent}
    modelProperties
    always {doNothing}
    eventually {not modelProperties or {
        some Item or some Email or some EmailContent
    }}
}

test expect {
  doNothingTracesUnsat: {doNothingTraces}
  for exactly 3 Person,
      exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
      exactly 1 EmailServer, exactly 2 Inbox,
      5 Item, 5 File, 2 Folder,
      3 EmailContent, 3 Email
  is unsat
}

-- Test that createFile, createFolder, and moveItem cannot violate modelProperties or ownership or create new Emails or EmailContents.
pred createAndMoveViolationTraces {
    {no Item and no Email and no EmailContent}
    modelProperties
    always {
        doNothing or {
            some p: (Person - Server), l: Location | { createFile[p, l] }
        } or {
            some p: (Person - Server), l: Location | { createFolder[p, l] }
        } or {
            some p: Person, m: File, d: Folder | { moveItem[p, m, d] }
        }
    }
    eventually {not modelProperties or {
       some Email or some EmailContent
    }}
}

test expect {
  createAndMoveViolationTracesUnsat: {createAndMoveViolationTraces}
  for exactly 3 Person,
      exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
      exactly 1 EmailServer, exactly 2 Inbox,
      5 Item, 5 File, 2 Folder,
      3 EmailContent, 3 Email
  is unsat
}

-- Boop

-- Test that an item must be in a drive to be in another drive's shared_with_me.
pred itemNotInDriveButShared {
    some i: Item | i not in Drive.location_items and i in Drive.shared_with_me
}

test expect {
  itemNotInDriveButSharedUnsat: {modelProperties and itemNotInDriveButShared}
  for exactly 3 Person,
      exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
      exactly 1 EmailServer, exactly 2 Inbox,
      5 Item, 5 File, 2 Folder,
      3 EmailContent, 3 Email
  is unsat
}

-- That that the email server must be owned by the Server person.
pred wrongServerOwnership {
    EmailServer.location_owner != Server
}

test expect {
  wrongServerOwnershipUnsat: {modelProperties and wrongServerOwnership}
  for exactly 3 Person,
      exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
      exactly 1 EmailServer, exactly 2 Inbox,
      5 Item, 5 File, 2 Folder,
      3 EmailContent, 3 Email
  is unsat
}

-- Test that an attached item must be on the email server.
pred attachedItemNotOnServer {
    some a: Attachment | (a.attached.location != EmailServer) or { 
        (some a.attached.folder_items and a.attached.folder_items.location != EmailServer)
    }
}

test expect {
  attachedItemNotOnServerUnsat: {modelProperties and attachedItemNotOnServer}
  for exactly 3 Person,
      exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
      exactly 1 EmailServer, exactly 2 Inbox,
      5 Item, 5 File, 2 Folder,
      3 EmailContent, 3 Email
  is unsat
}

-- Test that createFile and shareItem is sat.
pred createAndShareValidTraces {
    {no Item and no Email and no EmailContent}
    modelProperties
    always {
        doNothing or {
            some p: (Person - Server), l: Location | { createFile[p, l] }
        } or {
            some disj p, t: (Person - Server), i: Item | { shareItem[p, i, t] }
        }
    }
    eventually {some Email and some File}
}

test expect {
  createAndShareIsSAT: {createAndShareValidTraces}
  for exactly 3 Person,
      exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
      exactly 1 EmailServer, exactly 2 Inbox,
      5 Item, 5 File, 2 Folder,
      3 EmailContent, 3 Email
  is sat
}

-- Test that createFile and shareItem cannot violate modelProperties.
pred createAndShareViolationTraces {
    {no Item and no Email and no EmailContent}
    modelProperties
    always {
        doNothing or {
            some p: (Person - Server), loc: Location | { createFile[p, loc] }
        } or {
            some disj p, t: (Person - Server), i: Item | { shareItem[p, i, t] }
        }
    }
    eventually {not modelProperties}
}

test expect {
  createAndMoveViolationTracesUnsat: {createAndShareViolationTraces}
  for exactly 3 Person,
      exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
      exactly 1 EmailServer, exactly 2 Inbox,
      5 Item, 5 File, 2 Folder,
      3 EmailContent, 3 Email
  is unsat
}