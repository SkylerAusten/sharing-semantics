const stage = new Stage();

polypoints = [
    {x:100, y:200},
    {x:200, y:200},
    {x:175, y:150},
    {x:200, y:100},
    {x:1000, y:1200},
    {x:100, y:200}
]

let line = new Line({
    points: polypoints, 
    color: 'black', 
    width: 5, 
    arrow: false,
    style: "dotted"
});

stage.add(line);

stage.render(svg);