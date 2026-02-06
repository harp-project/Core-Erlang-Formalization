class GraphViewer {
    constructor() {
        this.cy = null;
        this.initializeCytoscape();
        this.setupEventListeners();
    }

    initializeCytoscape() {
        this.cy = cytoscape({
            container: document.getElementById('cy'),
            style: [
                {
                    selector: 'node',
                    style: {
                        "width": 2,
                        "height": 2,
                        'background-color': '#ea98ea',
                        // 'label': 'data(label)',
                        'text-valign': 'center',
                        'text-halign': 'center',
                        'color': 'black',
                        'padding': '10px'
                    }
                },
                {
                    selector: 'edge',
                    style: {
                        'width': 2,
                        'line-color': '#999',
                        'target-arrow-color': '#999',
                        'target-arrow-shape': 'triangle',
                        'arrow-scale': 3,
                        'curve-style': 'bezier',
                        'label': 'data(label)',
                        'text-rotation': 'autorotate',
                        'text-margin-y': -10,
                        'font-size': '12rem',
                    }
                }
            ],
        });
    }

    setupEventListeners() {
        document.addEventListener('graphLoaded', (event) => {
            this.loadGraph(event.detail);
        });
    }

    loadGraph(graphData) {
        // Clear existing graph
        this.cy.elements().remove();

        // Add new elements
        this.cy.add(graphData.elements);

        // Fit the graph to the container
        this.cy.fit();

        this.cy.layout({
            name: 'cola',
            maxSimulationTime: 100000,
        }).run();

        // Enable node dragging
        this.cy.nodes().ungrabify(false);
    }
}

// Initialize the graph viewer
const graphViewer = new GraphViewer(); 