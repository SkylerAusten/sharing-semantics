#lang forge/temporal

open "file_sharing.frg"

option max_tracelength 2
option min_tracelength 2


pred twoFilesMoveInit {
    some disj fold1, fold2: Folder, file1, file2, file3, file4: File | {
        fold1.folder_items = file1 + file2
        fold2.folder_items = file3 + file4
    }
}

pred twoFilesMoveFinal {
    some disj fold1, fold2: Folder, file1, file2, file3, file4: File | {
        fold1.folder_items = File
    }
}

pred twoFilesMoveTraces {
    twoFilesMoveInit
    modelProperties and ownership
    always {
        doNothing or {
            some p: Person, m: File, d: Folder | { moveItem[p, m, d] }
        }
    }
    eventually {always {twoFilesMoveFinal}}
}

-- Test that two files cannot move in one transition (but is possible in 2).
-- Confirmed UNSAT.
test expect { twoFilesMoveTracesUnsat: {twoFilesMoveTraces} for exactly 3 Person,
    exactly 5 Location, exactly 2 Drive, exactly 2 Computer, 
    exactly 1 EmailServer, exactly 2 Inbox,
    6 Item, 4 File, 2 Folder,
    0 EmailContent, 0 Email
is unsat }