class GraphLoader {
    constructor() {
        this.fileInput = document.getElementById('fileInput');
        this.setupEventListeners();
    }

    setupEventListeners() {
        this.fileInput.addEventListener('change', (event) => {
            const file = event.target.files[0];
            if (file) {
                this.readFile(file);
            }
        });
    }

    readFile(file) {
        const reader = new FileReader();
        
        reader.onload = (event) => {
            try {
                const graphData = JSON.parse(event.target.result);
                if (this.validateGraphData(graphData)) {
                    // Dispatch custom event with graph data
                    const graphEvent = new CustomEvent('graphLoaded', { detail: graphData });
                    document.dispatchEvent(graphEvent);
                } else {
                    alert('Invalid graph data format. Please check the JSON structure.');
                }
            } catch (error) {
                alert('Error reading file: ' + error.message);
            }
        };

        reader.onerror = () => {
            alert('Error reading file');
        };

        reader.readAsText(file);
    }

    validateGraphData(data) {
        return data && 
               data.elements;
    }
}

// Initialize the graph loader
const graphLoader = new GraphLoader(); 