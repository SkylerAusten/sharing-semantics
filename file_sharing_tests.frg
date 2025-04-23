#lang forge/temporal

open "file_sharing.frg"

option max_tracelength 12
option min_tracelength 8

// option solver MiniSatProver
// option core_minimization rce
// option logtranslation 1
// option coregranularity 1

------------------------ Model Constraint Tests ------------------------

-- Test that a file in a location_items other than its own location is unsat.
pred itemInTwoLocations {
    some disj l1, l2: Location, i: Item | i.location = l1 and i in l2.location_items
}

-- Confirmed UNSAT.
// test expect { itemInTwoLocationsUnsat: {modelProperties and itemInTwoLocations} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     1 Item, 1 File, 1 Folder,
//     0 EmailContent, 0 Email
// is unsat }


-- Test that a file being on a computer and being shared with someone.
pred sharedComputerItem {
    some i: Item | i.location in Computer and some i.shared_with or {
        some i: Item | i.location in Computer and i in Drive.shared_with_me
    }
}

-- Confirmed UNSAT.
// test expect { sharedComputerItemUnsat: {modelProperties and sharedComputerItem} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     1 Item, 1 File, 1 Folder,
//     0 EmailContent, 0 Email
// is unsat }

-- Test that an item cannot be shared with its owner.
pred itemSharedWithOwner {
    some i: Item | i.item_owner in i.shared_with
}

-- Confirmed UNSAT.
// test expect { itemSharedWithOwnerUnsat: {modelProperties and itemSharedWithOwner} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     1 Item, 1 File, 1 Folder,
//     0 EmailContent, 0 Email
// is unsat }

-- Test that an item's location must have the same location_owner as the item's item_owner.
pred mismatchedItemLocationOwner {
    some i: Item | i.location.location_owner != i.item_owner
}

-- Confirmed UNSAT.
// test expect { mismatchedItemLocationOwnerUnsat: {modelProperties and mismatchedItemLocationOwner} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     1 Item, 1 File, 1 Folder,
//     0 EmailContent, 0 Email
// is unsat }

-- All same_content relations are reciprocal.
pred nonReciprocalSameContent {
    some disj f1, f2: File | f2 in f1.same_content and not (f1 in f2.same_content)
}

-- Confirmed UNSAT.
// test expect { nonReciprocalSameContentUnsat: {modelProperties and nonReciprocalSameContent} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     2 Item, 2 File, 0 Folder,
//     0 EmailContent, 0 Email
// is unsat }

-- No item can be in more than one folder's items.
pred itemInMultipleFolders {
    some disj f1, f2: Folder, i: Item | (i in f1.folder_items) and (i in f2.folder_items)
}

-- Confirmed UNSAT.
// test expect { itemInMultipleFoldersUnsat: {modelProperties and itemInMultipleFolders} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     3 Item, 1 File, 2 Folder,
//     0 EmailContent, 0 Email
// is unsat }


-- Test that no two emails can have the same content.
pred duplicateEmailContent {
    some disj e1, e2: Email | e1.email_content = e2.email_content
}

-- Test that this combination of max items and the preds are individually SAT.
-- Confirmed SAT.
// test expect { duplicateEmailContentSat1: {duplicateEmailContent} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     1 Item, 1 File, 0 Folder,
//     1 EmailContent, 2 Email
// is sat }

-- Confirmed SAT.
// test expect { duplicateEmailContentSat2: {modelProperties} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     1 Item, 1 File, 0 Folder,
//     1 EmailContent, 2 Email
// is sat }

-- Confirmed UNSAT.
// test expect { duplicateEmailContentUnsat: {modelProperties and duplicateEmailContent} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     1 Item, 1 File, 0 Folder,
//     1 EmailContent, 2 Email
// is unsat }

-- Test that an item must be in a drive to be in another drive's shared_with_me.
pred itemNotInDriveButShared {
    some i: Item | i not in Drive.location_items and i in Drive.shared_with_me
}

-- Confirmed UNSAT.
// test expect { itemNotInDriveButSharedUnsat: {modelProperties and itemNotInDriveButShared} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     1 Item, 1 File, 1 Folder,
//     0 EmailContent, 0 Email
// is unsat }

-- That that the email server must be owned by the Server person.
pred wrongServerOwnership {
    EmailServer.location_owner != Server
}

-- Confirmed UNSAT.
// test expect { wrongServerOwnershipUnsat: {modelProperties and wrongServerOwnership} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     3 Item, 2 File, 2 Folder,
//     0 EmailContent, 0 Email
// is unsat }

-- Test that an item in the email map must be on the email server.
-- TODO: Fix
// pred itemInEmailMapNotOnServer {
//     some e: Email, i: Item | e->i in EmailServer.email_map and i.location != EmailServer
// }

// -- Confirmed UNSAT.
// // test expect { itemInEmailMapNotOnServerUnsat: {modelProperties and itemInEmailMapNotOnServer} for exactly 3 Person,
// //     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
// //     exactly 1 EmailServer, exactly 2 Inbox,
// //     3 Item, 2 File, 2 Folder,
// //     0 EmailContent, 1 Email
// // is unsat }

// -- Test that this holds true for folder content, too.
// pred itemsInEmailMapNotOnServer {
//     some e: Email, folder: Folder, file: File | {
//         e->folder in EmailServer.email_map
//         folder.location = EmailServer
//         file in folder.folder_items
//         file.location != EmailServer
//     }
// }

-- Confirmed UNSAT.
// test expect { itemsInEmailMapNotOnServerUnsat: {modelProperties and itemsInEmailMapNotOnServer} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     3 Item, 2 File, 2 Folder,
//     0 EmailContent, 1 Email
// is unsat }


-- Test that an attached item must be on the email server.
pred attachedItemNotOnServer {
    some a: Attachment | (a.attached.location != EmailServer or a.attached.^folder_items.location != EmailServer)
}

-- Confirmed UNSAT.
// test expect { attachedItemNotOnServerUnsat: {modelProperties and attachedItemNotOnServer} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     3 Item, 2 File, 2 Folder,
//     0 EmailContent, 0 Email
// is unsat }

-- Test that a linked item must be in a Drive.
pred linkedItemNotInDrive {
    some l: Link | l.points_to.location not in Drive or l.points_to.^folder_items.location not in Drive
}

-- Confirmed UNSAT.
// test expect { linkedItemNotInDriveUnsat: {modelProperties and linkedItemNotInDrive} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     3 Item, 2 File, 2 Folder,
//     0 EmailContent, 0 Email
// is unsat }

-- Test that an email in drafts cannot be in any inbox's sent or received.
pred emailInDraftsAndSentOrReceived {
    some disj i1, i2: Inbox, e: Email | e in i1.drafts and (e in i2.sent or e in i2.received or e in i1.sent or e in i1.received)
}

-- Confirmed UNSAT.
// test expect { emailInDraftsAndSentOrReceivedUnsat: {modelProperties and emailInDraftsAndSentOrReceived} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     3 Item, 2 File, 2 Folder,
//     1 EmailContent, 1 Email
// is unsat }

-- Test that Server cannot own a Drive, Computer, or Inbox.
pred serverOwnsProhibitedLocations {
    some d: Drive | d.location_owner = Server or {
        some c: Computer | c.location_owner = Server
    } or {
        some i: Inbox | i.inbox_owner = Server
    }
}

-- Confirmed UNSAT.
// test expect { serverOwnsProhibitedItemUnsat: {modelProperties and serverOwnsProhibitedLocations} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     3 Item, 2 File, 2 Folder,
//     1 EmailContent, 1 Email
// is unsat }

-- Test that all items in folders must have the same location as the folder.
pred itemFolderLocationMismatch {
    some file: File, folder: Folder | file in folder.folder_items and file.location != folder.location
}

-- Confirmed UNSAT.
// test expect { itemFolderLocationMismatchUnsat: {modelProperties and itemFolderLocationMismatch} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     4 Item, 3 File, 2 Folder,
//     0 EmailContent, 0 Email
// is unsat }

-- Test the sharing bijection for shared_with_me.
pred shareImplies {
    -- An item shared with someone must be in that person's drive's shared_with_me.
    all i: Item, p: Person | {p in i.shared_with implies {i in ((location_owner.p) & Drive).shared_with_me}}

    -- An item NOT shared with someone must NOT be in that person's drive's shared_with_me.
    all i: Item, p: Person | {p not in i.shared_with implies {i not in ((location_owner.p) & Drive).shared_with_me}}
}

-- Confirmed SAT.
// assert modelProperties is sufficient for shareImplies

pred doNothingTraces {
    {no Item and no Email and no EmailContent}
    modelProperties and ownership
    always {doNothing}
    eventually {not modelProperties or not ownership or {
        some Item or some Email or some EmailContent
    }}
}

-- Test that doNothing cannot violate modelProperties or ownership or create new Items, Emails, or EmailContents.
-- Confirmed UNSAT.
// test expect { doNothingViolationUnsat: {testTraces} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     3 Item, 3 File, 3 Folder,
//     2 EmailContent, 2 Email
// is unsat }


pred createAndMoveViolationTraces {
    {no Item and no Email and no EmailContent}
    modelProperties and ownership
    always {
        doNothing or {
            some p: (Person - Server), l: Location | { createFile[p, l] }
        } or {
            some p: (Person - Server), l: Location | { createFolder[p, l] }
        } or {
            some p: Person, m: File, d: Folder | { moveItem[p, m, d] }
        }
    }
    eventually {not modelProperties or not ownership or {
       some Email or some EmailContent
    }}
}

-- Test that createFile, createFolder, and moveItem cannot violate modelProperties or ownership or create new Emails or EmailContents.
-- Confirmed UNSAT.
// test expect { createAndMoveViolationUnsat: {createAndMoveViolationTraces} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     3 Item, 3 File, 3 Folder,
//     2 EmailContent, 2 Email
// is unsat }


pred createAndMoveItemsInit {
    no Item
    no Email
    no EmailContent
}

pred createAndMoveItemsMid {
    some disj f1, f2, f3: File, fold: Folder | {
        f1 + f2 + f3 in fold.folder_items
        fold.folder_items = File
    }
}

pred createAndMoveItemsFinal {
    some disj fold1, fold2: Folder, f1, f2, f3: File | {
        f1 + f2 in fold1.folder_items
        f3 in fold2.folder_items
        f1 + f2 + f3 = File
    }
}

pred createAndMoveTraces {
    createAndMoveItemsInit
    modelProperties and ownership
    always {
        doNothing or {
            some p: (Person - Server), l: Location | { createFile[p, l] }
        } or {
            some p: (Person - Server), l: Location | { createFolder[p, l] }
        } or {
            some p: Person, m: Item, d: Folder | { moveItem[p, m, d] }
        }
    }
    eventually {createAndMoveItemsMid}
    eventually {always {createAndMoveItemsFinal}}
}

-- Test that createFile, createFolder, and moveItem can create and move items into & out of folders.
-- Confirmed SAT.
// test expect { createAndMoveSat: {createAndMoveTraces} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     5 Item, 3 File, 3 Folder,
//     2 EmailContent, 2 Email
// is sat }

pred moveSharedInit {
    some disj fold1, fold2: Folder, file: File | {
        file in fold1.folder_items
        no file.shared_with
        no fold1.shared_with
        fold2.shared_with = Bob

        one fold1.location + fold2.location + file.location
    }
}

pred moveSharedFinal {
    some disj fold1, fold2: Folder, file: File | {
        file in fold2.folder_items
        file.shared_with = Bob
        no fold1.shared_with
        fold2.shared_with = Bob
    }
}

pred moveSharedViolationFinal {
    some disj fold1, fold2: Folder, file: File | {
        file in fold2.folder_items
        no file.shared_with
        no fold1.shared_with
        fold2.shared_with = Bob
    }
}

pred moveSharedTraces {
    moveSharedInit
    modelProperties and ownership
    always {
        doNothing or {
            some p: Person, m: Item, d: Folder | { moveItem[p, m, d] }
        }
    }
    eventually {always {moveSharedFinal}}
}

pred moveSharedViolationTraces {
    moveSharedInit
    modelProperties and ownership
    always {
        doNothing or {
            some p: Person, m: Item, d: Folder | { moveItem[p, m, d] }
        }
    }
    eventually {always {moveSharedViolationFinal}}
}

-- Test that moveItem can properly copy shared_with relations.
-- Confirmed SAT.
// test expect { moveSharedTracesSat: {moveSharedTraces} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     3 Item, 1 File, 2 Folder,
//     0 EmailContent, 0 Email
// is sat }

-- Test that moveItem properly copies folder shares to moved files.
-- Confirmed UNSAT.
// test expect { moveSharedViolationTracesUnsat: {moveSharedViolationTraces} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     3 Item, 1 File, 2 Folder,
//     0 EmailContent, 0 Email
// is unsat }


pred shareFilesInit {
    no Item
    no Email
    no EmailContent
}

pred shareFilesFinal {
    some disj e1, e2: Email | {
        some e1.to
        some e1.from
        some e1.email_content
        e1.email_content in Link
        some f: Folder | {
            some f.shared_with
            some f.folder_items
            e1.email_content.points_to = f
        }

        some e2.from
        some e2.to
    }
}

pred shareFilesTraces {
    shareFilesInit
    modelProperties and ownership
    always {
        doNothing or {
            some p: (Person - Server), l: Location | { createFile[p, l] }
        } or {
            some p: (Person - Server), l: Location | { createFolder[p, l] }
        } or {
            some p: Person, m: Item, d: Folder | { moveItem[p, m, d] }
        } or {
            some p: Person | { createEmail[p] }
        } or {
            some p, r: Person, e: Email | { setRecipients[p, e, r] }
        } or {
            some p: Person, e: Email | { addText[p, e] }
        } or {
            some p: Person, i: Item, e: Email | { addLink[p, i, e] }
        } or {
            some p: Person, e: Email | { sendEmail[p, e] }
        } or {
            some p: Person, e: Email | { removeEmailContent[p, e] }
        }
    }
    eventually {always {shareFilesFinal}}
}

pred shareFilesViolationTraces {
    shareFilesInit
    modelProperties and ownership
    always {
        doNothing or {
            some p: (Person - Server), l: Location | { createFile[p, l] }
        } or {
            some p: (Person - Server), l: Location | { createFolder[p, l] }
        } or {
            some p: Person, m: Item, d: Folder | { moveItem[p, m, d] }
        } or {
            some p: Person | { createEmail[p] }
        } or {
            some p, r: Person, e: Email | { setRecipients[p, e, r] }
        } or {
            some p: Person, e: Email | { addText[p, e] }
        } or {
            some p: Person, i: Item, e: Email | { addLink[p, i, e] }
        } or {
            some p: Person, e: Email | { sendEmail[p, e] }
        } or {
            some p: Person, e: Email | { removeEmailContent[p, e] }
        }
    }
    eventually {always {not modelProperties}}
}

-- Test that all the share transitions can produce a valid share.
-- Confirmed SAT.
// test expect { shareFilesTracesSat: {shareFilesTraces} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     4 Item, 2 File, 2 Folder,
//     2 EmailContent, 2 Email
// is sat }

-- Test that all the share transitions cannot violate modelProperties.
-- Suspected UNSAT, run hasn't finished.
// test expect { shareFilesViolationTracesUnsat: {shareFilesViolationTraces} for exactly 3 Person,
//     exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
//     exactly 1 EmailServer, exactly 2 Inbox,
//     4 Item, 2 File, 2 Folder,
//     2 EmailContent, 2 Email
// is unsat }

pred sendFilesInit {
    no Item
    no Email
    no EmailContent
}

pred sendFilesFinal {
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
}

pred sendFilesTraces {
    sendFilesInit
    modelProperties and ownership
    always {
        doNothing or {
            some p: (Person - Server), l: Location | { createFile[p, l] }
        } or {
            some p: (Person - Server), l: Location | { createFolder[p, l] }
        } or {
            some p: Person, m: Item, d: Folder | { moveItem[p, m, d] }
        } or {
            some p: Person | { createEmail[p] }
        } or {
            some p, r: Person, e: Email | { setRecipients[p, e, r] }
        } or {
            some p: Person, e: Email | { sendEmail[p, e] }
        } or {
            some p: Person, a: File, e: Email | { attachFile[p, a, e] }
        } or {
            some p: Person, a: Folder, e: Email | { attachFolder[p, a, e] }
        }
    }
    eventually {always {sendFilesFinal}}
}

-- Test that all the send transitions can produce a valid folder send.
-- Confirmed SAT.
test expect { sendFilesTracesSat: {sendFilesTraces} for exactly 3 Person,
    exactly 5 Location, exactly 2 Drive, exactly 2 Computer,
    exactly 1 EmailServer, exactly 2 Inbox,
    4 Item, 2 File, 2 Folder,
    1 EmailContent, 1 Email
is sat }

-- TODO: Test Unsat for this.

pred fullSendInit {
    no Item
    no Email
    no EmailContent
}

pred fullSendMid1 {

}

pred fullSendMid2 {

}

pred fullSendFinal {
    one e: Email | {
        some e.to
        some e.from
        some e.email_content
        e.email_content in Attachment
        some f: Folder | {
            some f.folder_items
            e.email_content.attached = f
        }
    }
}