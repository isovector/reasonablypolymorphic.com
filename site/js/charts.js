function pieChart(sel, csv, key, val) {
  document.querySelector(sel).textContent = ""

  d3.csv(csv).then((data) => {
  pie = d3.pie()
    .padAngle(0.005)
    .sort(null)
    .value(d => d[val])

  width = 500
  height = 500

  const radius = Math.min(width, height) / 2;
  arc = d3.arc().innerRadius(radius * 0.67).outerRadius(radius - 1);

  color = d3.scaleOrdinal()
    .domain(data.map(d => d[key]))
    .range(d3.quantize(t => d3.interpolateSpectral(t * 0.8 + 0.1), data.length).reverse())

  const arcs = pie(data);

  const svg = d3.select(sel).append("svg")
      .attr("viewBox", [-width / 2, -height / 2, width, height]);

  svg.selectAll("path")
    .data(arcs)
    .join("path")
      .attr("fill", d => color(d.data[key]))
      .attr("d", arc)
    .append("title")
      .text(d => `${d.data[key]}: ${d.data[val].toLocaleString()}`);

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
          .text(d => d.data[key]))
      .call(text => text.filter(d => (d.endAngle - d.startAngle) > 0.25).append("tspan")
          .attr("x", 0)
          .attr("y", "0.7em")
          .attr("fill-opacity", 0.7)
          .text(d => d.data[val].toLocaleString()));
  })
}

// NOTE: automagically casts the val column to a number
function lineChart(sel, csv, key, val) {
  document.querySelector(sel).textContent = ""
  d3.csv(csv).then(data => {
    width = 500
    height = 200
    margin = {top: 20, right: 30, bottom: 30, left: 40}
    yAxis = g => g
      .attr("transform", `translate(${margin.left},0)`)
      .call(d3.axisLeft(y))
      .call(g => g.select(".domain").remove())
      .call(g => g.select(".tick:last-of-type text").clone()
          .attr("x", 3)
          .attr("text-anchor", "start")
          .attr("font-weight", "bold")
          .text(data.y))
    xAxis = g => g
      .attr("transform", `translate(0,${height - margin.bottom})`)
      .call(d3.axisBottom(x).ticks(width / 80).tickFormat(y => `${y.toFixed(0)}`).tickSizeOuter(0))
    y = d3.scaleLinear()
      .domain([0, d3.max(data, d => +d[val])]).nice()
      .range([height - margin.bottom, margin.top])
    x = d3.scaleLinear()
      .domain(d3.extent(data, d => d[key]))
      .range([margin.left, width - margin.right])
    line = d3.line()
      .defined(d => !isNaN(d[val]))
      .x(d => x(d[key]))
      .y(d => y(d[val]))

    callout = (g, value) => {
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
            .style("font-weight", (_, i) => i ? null : "bold")
            .text(d => d));

      const {x, y, width: w, height: h} = text.node().getBBox();

      text.attr("transform", `translate(${-w / 2},${15 - y})`);
      path.attr("d", `M${-w / 2 - 10},5H-5l5,-5l5,5H${w / 2 + 10}v${h + 20}h-${w + 20}z`);
    }


    const bisect_helper = d3.bisector(d => d[key]).left;
    const bisect = mx => {
      const k = x.invert(mx);
      const index = bisect_helper(data, k, 1);
      const a = data[index - 1];
      const b = data[index];
      return b && (k - a[key] > b[key] - k) ? b : a;
    };

    const svg = d3.select(sel).append("svg")
        .attr("viewBox", [0, 0, width, height])
        .style("-webkit-tap-highlight-color", "transparent")
        .style("overflow", "visible");

    svg.append("g")
        .call(xAxis);

    svg.append("g")
        .call(yAxis);

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
        .attr("transform", `translate(${x(d[key])},${y(d[val])})`)
        .call(callout, `${val}: ${parseFloat(d[val]).toFixed(2)}
${key}: ${d[key]}`);
     });

    svg.on("touchend mouseleave", () => tooltip.call(callout, null));
  })
}

