function pieChart(sel, csv, get_key, get_val) {
  document.querySelector(sel).textContent = ""

  d3.csv(csv).then((data) => {
  const pie = d3.pie()
    .padAngle(0.005)
    .sort(null)
    .value(get_val)

  const width = 500
  const height = 500

  const radius = Math.min(width, height) / 2;
  const arc = d3.arc().innerRadius(radius * 0.67).outerRadius(radius - 1);

  const color = d3.scaleOrdinal()
    .domain(data.map(get_key))
    .range(d3.quantize(t => d3.interpolateSpectral(t * 0.8 + 0.1), data.length).reverse())

  const arcs = pie(data);

  const svg = d3.select(sel).append("svg")
      .attr("viewBox", [-width / 2, -height / 2, width, height])
      .attr("width", width)
      .attr("height", height);

  svg.selectAll("path")
    .data(arcs)
    .join("path")
      .attr("fill", d => color(get_key(d.data)))
      .attr("d", arc)
    .append("title")
      .text(d => `${get_key(d.data)}: ${get_val(d.data)}`);

  svg.append("g")
      .attr("font-family", "sans-serif")
      .attr("font-size", 12)
      .attr("text-anchor", "middle")
    .selectAll("text")
    .data(arcs)
    .join("text")
      .attr("transform", d => `translate(${arc.centroid(d)})`)
      .call(text => text.append("tspan")
          .attr("y", "-0.4em")
          .attr("font-weight", "bold")
          .text(d => get_key(d.data)))
      .call(text => text.filter(d => (d.endAngle - d.startAngle) > 0.25).append("tspan")
          .attr("x", 0)
          .attr("y", "0.7em")
          .attr("fill-opacity", 0.7)
          .text(d => get_val(d.data)));
  })
}

function lineChart(sel, csv, x_label, get_key, y_label, get_val) {
  document.querySelector(sel).textContent = ""
  d3.csv(csv).then(data => {
    const width = 500
    const height = 200
    const margin = {top: 20, right: 30, bottom: 30, left: 40}
    const yAxis = g => g
      .attr("transform", `translate(${margin.left},0)`)
      .call(d3.axisLeft(y))
      .call(g => g.select(".domain").remove())
      .call(g => g.select(".tick:last-of-type text").clone()
          .attr("x", 3)
          .attr("text-anchor", "start")
          .attr("font-weight", "bold")
          .text(data.y))
    const xAxis = g => g
      .attr("transform", `translate(0,${height - margin.bottom})`)
      .call(d3.axisBottom(x).ticks(width / 80).tickFormat(y => `${y}`).tickSizeOuter(0))
    const y = d3.scaleLinear()
      .domain([0, d3.max(data, get_val)]).nice()
      .range([height - margin.bottom, margin.top])
    const x = d3.scaleLinear()
      .domain(d3.extent(data, get_key))
      .range([margin.left, width - margin.right])
    const line = d3.line()
      .defined(d => !isNaN(get_val(d)))
      .x(d => x(get_key(d)))
      .y(d => y(get_val(d)))

    const callout = (g, value) => {
      if (!value) return g.style("display", "none");

      g
          .style("display", null)
          .style("pointer-events", "none")
          .style("font", "10px sans-serif");

      const path = g.selectAll("path")
        .data([null])
        .join("path")
          .attr("fill", "white")
          .attr("stroke", "black");

      const text = g.selectAll("text")
        .data([null])
        .join("text")
        .call(text => text
          .selectAll("tspan")
          .data((value + "").split(/\n/))
          .join("tspan")
            .attr("x", 0)
            .attr("y", (d, i) => `${i * 1.1}em`)
            // .style("font-weight", (_, i) => i ? null : "bold")
            .text(d => d));

      const {x, y, width: w, height: h} = text.node().getBBox();

      text.attr("transform", `translate(${-w / 2},${15 - y})`);
      path.attr("d", `M${-w / 2 - 10},5H-5l5,-5l5,5H${w / 2 + 10}v${h + 20}h-${w + 20}z`);
    }


    const bisect_helper = d3.bisector(get_key).left;
    const bisect = mx => {
      const k = x.invert(mx);
      const index = bisect_helper(data, k, 1);
      const a = data[index - 1];
      const b = data[index];
      return b && (k - get_key(a) > get_key(b) - k) ? b : a;
    };

    const svg = d3.select(sel).append("svg")
        .attr("viewBox", [0, 0, width, height])
        .style("-webkit-tap-highlight-color", "transparent")
        .style("overflow", "visible");

    svg.append("g")
        .call(xAxis);

    svg.append("text")
      .attr("transform",
            "translate(" + (width/2) + " ," +
                           (height + margin.top / 4) + ")")
      .style("text-anchor", "middle")
      .attr("font-size", "8pt")
      .text(x_label);

    svg.append("g")
        .call(yAxis);

  svg.append("text")
      .attr("transform", "rotate(-90)")
      .attr("y", 0 - margin.left / 10)
      .attr("x",0 - (height / 2))
      .attr("dy", "1em")
      .style("text-anchor", "middle")
      .attr("font-size", "8pt")
      .text(y_label);


    svg.append("path")
        .datum(data)
        .attr("fill", "none")
        .attr("stroke", "steelblue")
        .attr("stroke-width", 1.5)
        .attr("stroke-linejoin", "round")
        .attr("stroke-linecap", "round")
        .attr("d", line);

    const tooltip = svg.append("g");

    svg.on("touchmove mousemove", function(event) {
      const d = bisect(d3.pointer(event, this)[0]);

      tooltip
        .attr("transform", `translate(${x(get_key(d))},${y(get_val(d))})`)
        .call(callout, `X: ${get_key(d)}
Y: ${get_val(d)}`);
     });

    svg.on("touchend mouseleave", () => tooltip.call(callout, null));
  })
}

