# Sending vs. Sharing Files
This model is intended to model the real-world process of sending & sharing files, specifically to illustrate the difference in sending a file on a computer versus sharing something like a Google Doc in the ability to see updates made to the shared/sent files (e.g. emailed files will not reflect changes, shared Google Docs will).
The two primary traces I've set up in the system are shareFilesTraces and sendFilesTraces, which reflect sharing a Google Doc and sending a file on one's computer, respectively.

The end goal of this system is to build it into a larger application that allows users to interact with the model without knowing Forge.  The idea is that this approach can be used to illustrate computer systems and concepts with a temporal components to appropriate audiences, e.g. Paxos to Distributed Systems students, the TCP handshake to networking students, or this system to email users hoping to better understand sending and recieving files.

## Simplifications
TODO: Fill in.

## Model Sigs
#### Person
This is a sig representing email users.  Two specific named Persons are used, Bobbi and Joe.

#### Item
In this model, Items can be files and folders.  Folders can also contain a set of files.

#### Location
This is a sig representing locations where Items can be located (e.g. Bobbi's Google Drive or Joe's Computer).  The email server is a special location reserved for item copies created in the process of emailing a file or folder.

#### Email & EmailContent
Emails contain a single sender (from) and require one or more recipients (to) in order to be sent.  They must also have one content: a link (pointing to a Drive item), an attachment (of a computer item), or email text content.

#### Inbox
Each user in the system has one inbox, which contains sent, drafted, and recieved emails, as well as threads created by replying to emails.

#### Transition Tracker
The transition tracker is a debugging tool which points to the actor of each transition and which transition occured (e.g. creating a file, adding an attachment to an email, or doing nothing).

## Transitions
doNothing
Represents a state where no actions occur; typically used to denote a stable state or when the system reaches a final state. No properties or relationships in the model change, maintaining the current state without modification.

createFile
Handles the creation of a new file by a specific actor within a specific location that the actor owns. The actor must own the location where the file is being created. A new file is instantiated, assigned ownership and creation metadata, and it's placed within the actor's location. No shared or same_content relationships are established for the new file.

createFolder
Manages the creation of a new folder by an actor within a location they own. The actor must be the owner of the location. A new folder is created with no initial contents. The folder is associated with the actor's location and ownership is set to the actor.

moveItem
Moves an item (either a file or a folder) to a destination folder owned by the same actor. The actor must own both the item and the destination folder. The item cannot already be in the destination folder. The item is added to the destination folder's contents. If necessary, adjustments are made to shared_with properties to reflect the move.

createEmail
Initiates a new email draft for an actor. A new email object is created in the actor's drafts folder without any initial recipients or content.

setRecipients
Assigns recipients to an email that's currently in drafts. The email must be editable (still in drafts) and cannot include the server as a recipient. The recipient list of the email is updated to include one or more specified recipients.

removeRecipients
Clears all recipients from an email draft. The email must have recipients and be in the actor's drafts. The recipient list for the email is cleared.

attachFile
Attaches a file to an email draft. The file must be owned by the actor and be located on their computer. A reference to the file is attached to the email, and an entry is created in the email server's map linking the email to the attached file.

attachFolder
Attaches a folder and its contents to an email draft. The folder must be owned by the actor and located on their computer. The folder and its contents are cloned to the email server, and references to these clones are attached to the email.

addText
Adds text content to an email draft. The email must be in drafts and have no other content. A text content object is created and linked to the email.

addLink
Adds a hyperlink to an item within an email draft. The linked item must be accessible to the actor (either owned by or shared with them). A link object pointing to the item is created and added to the email's content.

removeEmailContent
Removes all content from an email draft. The email must have content and be in the actor's drafts. All content associated with the email is removed, including deleting any attachments from the email server.

sendEmail
Sends an email from the drafts to the specified recipients, moving it to the sent folder of the sender and the received folders of the recipients. The email must have a sender, recipients, and content. The email is removed from drafts and added to the appropriate sent and received folders. If the content includes links, the linked items are shared with the recipients.

sendReply
Sends a reply to a received email, linking the new email in a thread. The reply must be in drafts, and the original email must be in the received folder. The reply is sent to the original email's recipients, and a thread link is established between the original and the reply.

editFile
The item must be owned by or shared with the actor. The file loses all its same_contents, and changes are made to the same_content relationship for other items as necessary.

## theme.json
When running any traces, use theme.json to hide some of the less helpful relations & atoms.