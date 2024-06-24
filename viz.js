// Function to generate coordinates for each rectangle based on integer ID
function calculateLocationCoordinates(id) {
    const x = 100; // X coordinate for the rectangle
    const yBase = 50; // Base Y coordinate for the first rectangle
    const yOffset = 220; // Increased offset between rectangles vertically to accommodate taller rectangles

    const y = yBase + id * yOffset;
    return { x, y };
}

// Function to create a location rectangle with increased height
function createLocationRectangle(coords) {
    return new Rectangle({
        coords: coords,
        width: 500, // Width of the rectangle
        height: 190, // Increased height of the rectangle
        color: 'lightgrey',
    });
}

// Function to create a base rectangle for the folder with increased height
function createFolderBaseRectangle(coords, no_contained) {
    if (no_contained == 0) {
        return new Rectangle({
            coords: { x: coords.x, y: coords.y },
            width: 145, // Width of the base rectangle
            height: 115, // Height of the base rectangle
            color: 'peachpuff', // Manilla/peach color
        });
    }

    return new Rectangle({
        coords: { x: coords.x, y: coords.y },
        width: 80 + (115 * no_contained), // Width of the base rectangle
        height: 115, // Height of the base rectangle
        color: 'peachpuff', // Manilla/peach color
    });
}

// Function to create a tab rectangle for the folder
function createFolderTabRectangle(coords) {
    return new Rectangle({
        coords: { x: coords.x, y: coords.y },
        width: 40, // Width of the tab rectangle
        height: 20, // Height of the tab rectangle
        color: 'peachpuff', // Manilla/peach color
    });
}

// Function to create a file rectangle for the folder
function createFileRectangle(coords, location_type) {
    let color = "lightgreen";
    if (location_type == "Computer") {
        color = "lightblue";
    }

    if (location_type == "Server") {
        color = "salmon";
    }

    // Create the rectangle
    const rect = new Rectangle({
        coords: { x: coords.x, y: coords.y },
        width: 100, // Width of the rectangle
        height: 80, // Height of the rectangle
        color: color,
    });

    // Create an input field
    const input = document.createElement('input');
    input.type = 'text';
    input.value = "filler";
    input.style.position = 'absolute';
    input.style.left = `${coords.x + 10}px`;
    input.style.top = `${coords.y + 30}px`;
    input.style.width = '80px';
    input.style.height = '20px';
    input.style.backgroundColor = 'transparent';
    input.style.border = 'none';
    input.style.textAlign = 'center';
    input.style.color = 'black';

    // Append the input field to the SVG container
    document.getElementById('svg-container').appendChild(input);

    // Event listener to update the rectangle's tooltip when the input value changes
    input.addEventListener('input', () => {
        rect.tooltip = input.value;
    });

    return rect;
}

// Function to create an arrow for shared files
function createSharedFileArrow(coords) {
    const arrowWidth = 150;
    const arrowHeight = 50;
    const shaftWidth = 100;
    const arrowHeadWidth = 50;

    // Create the arrow's shaft
    const shaft = new Rectangle({
        coords: { x: coords.x, y: coords.y },
        width: shaftWidth,
        height: arrowHeight,
        color: 'orange',
    });

    // Create the arrow's head using Polygon
    const arrowHeadPoints = [
        { x: coords.x + shaftWidth, y: coords.y },
        { x: coords.x + shaftWidth + arrowHeadWidth, y: coords.y + arrowHeight / 2 },
        { x: coords.x + shaftWidth, y: coords.y + arrowHeight }
    ];

    const arrowHead = new Polygon({
        points: arrowHeadPoints,
        color: 'orange',
        borderWidth: 2,
        borderColor: 'black'
    });

    // Create an input field on the shaft
    const input = document.createElement('input');
    input.type = 'text';
    input.value = "filler";
    input.style.position = 'absolute';
    input.style.left = `${coords.x + 10}px`;
    input.style.top = `${coords.y + 15}px`;
    input.style.width = '80px';
    input.style.height = '20px';
    input.style.backgroundColor = 'transparent';
    input.style.border = 'none';
    input.style.textAlign = 'center';
    input.style.color = 'black';

    // Append the input field to the SVG container
    document.getElementById('svg-container').appendChild(input);

    // Event listener to update the shaft's tooltip when the input value changes
    input.addEventListener('input', () => {
        shaft.tooltip = input.value;
    });

    return { shaft, arrowHead };
}

// Function to create a text label
function createLocationLabel(coords, label) {
    return new TextBox({
        text: label,
        coords: { x: coords.x + 250, y: coords.y + 175 }, // Adjusted to be centered below the taller rectangle
        color: 'black',
        fontSize: 20,
        textAlign: 'center',
    });
}

// Main function to generate the visualization
function generateVisualization(locations) {
    const stage = new Stage();

    for (const [location_id, location_data] of Object.entries(locations)) {
        const location_name = location_data.name;
        const location_type = location_data.type;

        const location_coords = calculateLocationCoordinates(parseInt(location_id));

        stage.add(createLocationRectangle(location_coords));
        stage.add(createLocationLabel(location_coords, location_name));

        let file_x = location_coords.x + 25;
        let file_y = location_coords.y + 25;

        // Process and add shared files as arrows
        for (const shared_file of location_data["shared-files"]) {
            const arrow = createSharedFileArrow({ x: file_x, y: file_y + 15 });
            stage.add(arrow.shaft);
            stage.add(arrow.arrowHead);
            file_x += 180;
        }

        // Process and add folderless files
        for (const file_name of location_data["no-folder"]) {
            stage.add(createFileRectangle({ x: file_x, y: file_y }, location_type));
            file_x = file_x + 120;
        }

        let folder_x = file_x;
        let folder_y = location_coords.y + 15;

        for (const [folder_id, folder_data] of Object.entries(location_data.folders)) {
            const contained_files = folder_data["files"];
            const no_contained = contained_files.length;

            stage.add(createFolderBaseRectangle({ x: folder_x, y: folder_y }, no_contained));
            stage.add(createFolderTabRectangle({ x: folder_x, y: folder_y }));

            file_x = folder_x + 50;
            file_y = folder_y + 10;

            for (const file_name of folder_data["files"]) {
                stage.add(createFileRectangle({ x: file_x, y: file_y }, location_type));
                file_x = file_x + 120;
            }

            if (no_contained == 0) {
                folder_x = folder_x + 160;
            } else {
                folder_x = folder_x + 90 + (120 * no_contained);
            }
        }
    }

    stage.render(svg);
}

// Example usage
const locations = {
    0: {
        "name": "JoeDrive0",
        "type": "Drive",
        "folders": {
            0: {"name": "Folder0", "files": ["File0", "File1", "File2"]},
            1: {"name": "Folder1", "files": ["File3"]},
            2: {"name": "Folder1", "files": ["File3", "File2"]},
            3: {"name": "Folder1", "files": []},
            4: {"name": "Folder1", "files": []},
            5: {"name": "Folder1", "files": []},
        },
        "no-folder": ["File4", "File3"],
        "shared-folders": {
            0: {"name": "Folder0", "files": ["File0", "File1", "File2"]},
            1: {"name": "Folder1", "files": ["File3"]},
        },
        "shared-files": ["File4"],
    },
    1: {
        "name": "JoeComputer0",
        "type": "Computer",
        "folders": {
            0: {"name": "Folder2", "files": ["File5", "File6", "File5", "File6"]},
            1: {"name": "Folder3", "files": []},
        },
        "no-folder": ["File6"],
        "shared-folders": {
            0: {"name": "Folder0", "files": ["File0", "File1", "File2"]},
            1: {"name": "Folder1", "files": ["File3"]},
        },
        "shared-files": ["File4"],
    },
    2: {
        "name": "EmailServer",
        "type": "Server",
        "folders": {},
        "no-folder": ["File3"],
        "shared-folders": {
            0: {"name": "Folder0", "files": ["File0", "File1", "File2"]},
            1: {"name": "Folder1", "files": ["File3"]},
        },
        "shared-files": ["File4"],
    },
};

generateVisualization(locations);
