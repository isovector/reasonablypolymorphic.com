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


