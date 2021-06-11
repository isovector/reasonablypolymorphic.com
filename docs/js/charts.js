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
        .style("overflow", "visible")
        .attr("width", width)
        .attr("height", height);

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

    const grid = g => g
      .attr("stroke", "currentColor")
      .attr("stroke-opacity", 0.1)
      .call(g => g.append("g")
        .selectAll("line")
        .data(x.ticks())
        .join("line")
          .attr("x1", d => 0.5 + x(d))
          .attr("x2", d => 0.5 + x(d))
          .attr("y1", margin.top)
          .attr("y2", height - margin.bottom))
      .call(g => g.append("g")
        .selectAll("line")
        .data(y.ticks())
        .join("line")
          .attr("y1", d => 0.5 + y(d))
          .attr("y2", d => 0.5 + y(d))
          .attr("x1", margin.left)
          .attr("x2", width - margin.right));

    svg.append("g")
        .call(grid);

    svg.append("text")
        .attr("transform", "rotate(-90)")
        .attr("y", 0 - margin.left / 2)
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

function sankey(sel, csv) {
  document.querySelector(sel).textContent = ""
  d3.csv(csv).then(data => {
    const keys = data.columns.slice(0, -1)
    const val_key = data.columns.slice(-1)
    const color = d3.scaleOrdinal(["en"], ["#da4f81"]).unknown("#4f81da")

    const width = 975
    const height = 720

    const graph = (() => {
      let index = -1;
      const nodes = [];
      const nodeByKey = new Map;
      const indexByKey = new Map;
      const links = [];

      for (const k of keys) {
        for (const d of data) {
          const key = JSON.stringify([k, d[k]]);
          if (nodeByKey.has(key)) continue;
          const node = {name: d[k]};
          nodes.push(node);
          nodeByKey.set(key, node);
          indexByKey.set(key, ++index);
        }
      }

      for (let i = 1; i < keys.length; ++i) {
        const a = keys[i - 1];
        const b = keys[i];
        const prefix = keys.slice(0, i + 1);
        const linkByKey = new Map;
        for (const d of data) {
          const names = prefix.map(k => d[k]);
          const key = JSON.stringify(names);
          const value = +d[val_key] || 1;
          let link = linkByKey.get(key);
          if (link) { link.value += value; continue; }
          link = {
            source: indexByKey.get(JSON.stringify([a, d[a]])),
            target: indexByKey.get(JSON.stringify([b, d[b]])),
            names,
            value
          };
          links.push(link);
          linkByKey.set(key, link);
        }
      }

      return {nodes, links};
    })()

    sankey = d3.sankey()
      .nodeSort(null)
      .linkSort(null)
      .nodeWidth(4)
      .nodePadding(8)
      .extent([[0, 5], [width, height - 5]])

    const svg = d3.select(sel).append("svg")
      .attr("width", width)
      .attr("height", height)
      .attr("viewBox", [0, 0, width, height]);

    const {nodes, links} = sankey({
      nodes: graph.nodes.map(d => Object.assign({}, d)),
      links: graph.links.map(d => Object.assign({}, d))
    });

    svg.append("g")
      .selectAll("rect")
      .data(nodes)
      .join("rect")
        .attr("x", d => d.x0)
        .attr("y", d => d.y0)
        .attr("height", d => d.y1 - d.y0)
        .attr("width", d => d.x1 - d.x0)
      .append("title")
        .text(d => `${d.name}\n${d.value.toLocaleString()}`);

    svg.append("g")
        .attr("fill", "none")
      .selectAll("g")
      .data(links)
      .join("path")
        .attr("d", d3.sankeyLinkHorizontal())
        .attr("stroke", d => color(d.names[0]))
        .attr("stroke-width", d => d.width)
        .style("mix-blend-mode", "multiply")
      .append("title")
        .text(d => `${d.names.join(" → ")}\n${d.value.toLocaleString()}`);

    svg.append("g")
        .style("font", "10px sans-serif")
      .selectAll("text")
      .data(nodes)
      .join("text")
        .attr("x", d => d.x0 < width / 2 ? d.x1 + 6 : d.x0 - 6)
        .attr("y", d => (d.y1 + d.y0) / 2)
        .attr("dy", "0.35em")
        .attr("text-anchor", d => d.x0 < width / 2 ? "start" : "end")
        .text(d => d.name)
      .append("tspan")
        .attr("fill-opacity", 0.7)
        .text(d => ` ${d.value.toLocaleString()}`);


  })
}

function stackedArea(sel, csv, get_time, get_key, get_count, get_name) {
  document.querySelector(sel).textContent = ""
  d3.csv(csv).then(predata => {
    var cols_set = {}
    for (var i = 0; i < predata.length; i++) {
      const row = predata[i]
      const key = get_key(row)
      cols_set[key] = key
    }

    const cols = Object.keys(cols_set)

    var rows = {}
    for (var i = 0; i < predata.length; i++) {
      const row = predata[i]
      const time = get_time(row)
      if (rows[time] == undefined) {
        rows[time] = {time: time}
        for (var j = 0; j < cols.length; j++) {
          rows[time][cols[j]] = 0
        }
      }
      rows[get_time(row)][get_key(row)] = get_count(row)
    }

    var data = []
    const keys = Object.keys(rows).map(d => +d).sort()
    for (var i = 0; i < keys.length; i++) {
      data.push(rows[keys[i]])
    }

    const margin = ({top: 20, right: 30, bottom: 30, left: 40})
    const height = 300
    const width = 500

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
      .call(
        d3.axisBottom(x)
          .ticks(width / 40)
          .tickFormat(y => `${+y}`)
         .tickSizeOuter(0))

    const time_col = "time"

    const color = d3.scaleOrdinal()
      .domain(cols)
      .range(d3.schemeCategory10)

    const series = d3.stack().keys(cols)(data)

    const y = d3.scaleLinear()
      .domain([0, d3.max(series, d => d3.max(d, d => d[1]))]).nice()
      .range([height - margin.bottom, margin.top])

    const x = d3.scaleUtc()
      .domain(d3.extent(data, d => +d[time_col]))
      .range([margin.left, width - margin.right])

    const area = d3.area()
      .x(d => x(+d.data[time_col]))
      .y0(d => y(d[0]))
      .y1(d => y(d[1]))

    const svg = d3.select(sel).append("svg")
      .attr("width", width)
      .attr("height", height)
      .attr("viewBox", [0, 0, width, height]);

    svg.append("g")
      .selectAll("path")
      .data(series)
      .join("path")
        .attr("fill", ({key}) => color(key))
        .attr("d", area)
      .append("title")
        .text(({key}) => key);

    svg.append("g")
        .call(xAxis);

    svg.append("g")
        .call(yAxis);

  })
}

function dotChart(sel, csv, get_x, get_y, get_size, get_color, get_name) {
  document.querySelector(sel).textContent = ""
  d3.csv(csv).then(data => {

    const margin = ({top: 20, right: 30, bottom: 30, left: 40})

    const width = 600
    const height = 300

    const values = [...new Set(data.map(get_y))]
    const num_values = values.length

    const row_height = (height - margin.top - margin.bottom) / (num_values)

    data = d3.map(data, d => {
      d.xrand = (Math.random() - 0.5) * 5
      d.yrand = -Math.random() * row_height
      return d
    })

    const yAxis = g => g
      .attr("transform", `translate(${margin.left},0)`)
      .call(d3.axisLeft(y).ticks(null, "+"))
      .call(g => g.select(".domain").remove())
      .call(g => g.selectAll(".tick line")
        .filter(d => d === 0)
        .clone()
          .attr("x2", width - margin.right - margin.left)
          .attr("stroke", "#ccc"))
      .call(g => g.append("text")
          .attr("fill", "#000")
          .attr("x", 5)
          .attr("y", margin.top)
          .attr("dy", "0.32em")
          .attr("text-anchor", "start")
          .attr("font-weight", "bold"))
          // .text("Anomaly (°C)"))

    const xAxis = g => g
      .attr("transform", `translate(0,${height - margin.bottom})`)
      .call(d3.axisBottom(x).ticks(width / 80).tickFormat(y => `${+y}`)
                            .tickSizeOuter(0))
      // .call(g => g.select(".domain").remove())

    const max = d3.max(data, d => Math.abs(get_color(d)));
    const color = d3.scaleOrdinal(d3.schemeCategory10).domain([max, -max]);

    const y = d3.scalePoint()
      .domain(d3.map(data, get_y)) // .nice()
      .range([height - margin.bottom, margin.top])

    const xpos = d => x(get_x(d)) + d.xrand
    const ypos = d => y(get_y(d)) + d.yrand

    const x = d3.scaleUtc()
      .domain(d3.extent(data, get_x))
      .range([margin.left, width - margin.right])

    const sz = d3.scaleLinear()
      .domain(d3.extent(data, get_size)).nice()
      .range([2, 10]);

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
            .style("font-weight", (_, i) => i ? null : "bold")
            .text(d => d));

      const {x, y, width: w, height: h} = text.node().getBBox();

      text.attr("transform", `translate(${-w / 2},${15 - y})`);
      path.attr("d", `M${-w / 2 - 10},5H-5l5,-5l5,5H${w / 2 + 10}v${h + 20}h-${w + 20}z`);
    }

    const svg = d3.select(sel).append("svg")
      .attr("width", width)
      .attr("height", height)
      .attr("viewBox", [0, 0, width, height])
      .style("overflow", "visible");

    svg.append("g")
        .call(xAxis);

    svg.append("g")
        .call(yAxis);

    const grid = g => g
      .attr("stroke", "currentColor")
      .attr("stroke-opacity", 0.1)
      .call(g => g.append("g")
        .selectAll("line")
        .data(x.ticks())
        .join("line")
          .attr("x1", d => 0.5 + x(d))
          .attr("x2", d => 0.5 + x(d))
          .attr("y1", margin.top)
          .attr("y2", height - margin.bottom))
      .call(g => g.append("g")
        .selectAll("line")
        .data(values)
        .join("rect")
          .attr("y", d => 0.5 + y(d) - row_height)
          .attr("height", d => row_height)
          .attr("x", margin.left)
          .attr("width", width - margin.right - margin.left)
          .attr("fill-opacity", 0.2)
          .attr("fill", d => color(d)));

    svg.append("g")
        .call(grid);

    svg.append("g")
        .attr("stroke", "#000")
        .attr("stroke-opacity", 0.2)
      .selectAll("circle")
      .data(data)
      .join("circle")
        .attr("cx", d => xpos(d))
        .attr("cy", d => ypos(d))
        .attr("fill", d => color(get_color(d)))
        .attr("r", d => sz(get_size(d)))
      .on("touchend mouseleave", (event, d) => {
        tooltip
          .call(callout, null);
      })
      .on("touchstart mouseenter", (event, d) => {
        tooltip
          .attr("transform", `translate(${xpos(d)},${ypos(d)})`)
          .call(callout, `${get_name(d)}
X: ${get_x(d)}
Y: ${get_y(d)}
Size: ${get_size(d)}
Color: ${get_color(d)}
`);
      })
      .append("title")
        .text(get_name);

    const tooltip = svg.append("g");

  })
}

function truncateString(str, num) {
  if (str.length > num) {
    return str.slice(0, num) + "...";
  } else {
    return str;
  }
}

function multiLineChart(sel, csv, get_key, get_x, get_y) {
  document.querySelector(sel).textContent = ""
  d3.csv(csv).then(data => {
    const width = 500
    const height = 200
    const margin = {top: 20, right: 30, bottom: 30, left: 40}

    const keys = [...new Set(data.map(get_key))]
    const x_vals = [...new Set(data.map(get_x))]

    const x = d3.scaleLinear()
      .domain(d3.extent(x_vals))
      .range([margin.left, width - margin.right])

    const y = d3.scaleLinear()
      .domain([0, d3.max(data, get_y)]).nice()
      .range([height - margin.bottom, margin.top])

    const color = d3.scaleOrdinal()
      .domain(keys)
      .range(d3.schemeCategory10)

    const xAxis = g => g
      .attr("transform", `translate(0,${height - margin.bottom})`)
      .call(d3.axisBottom(x).ticks(width / 80).tickFormat(y => `${+y}`).tickSizeOuter(0))

    const yAxis = g => g
      .attr("transform", `translate(${margin.left},0)`)
      .call(d3.axisLeft(y))
      .call(g => g.select(".domain").remove())
      .call(g => g.select(".tick:last-of-type text").clone()
          .attr("x", 3)
          .attr("text-anchor", "start")
          .attr("font-weight", "bold")
          .text(data.y))

    const line = d3.line()
      // .defined(d => !isNaN(d))
      .x((d, i) => x(get_x(d)))
      .y(d => y(get_y(d)))

    const svg = d3.select(sel).append("svg")
      .attr("width", width)
      .attr("height", height)
      .attr("viewBox", [0, 0, width, height])
      .style("overflow", "visible");

    svg.append("g")
        .call(xAxis);

    svg.append("g")
        .call(yAxis);

    const grid = g => g
      .attr("stroke", "currentColor")
      .attr("stroke-opacity", 0.1)
      .call(g => g.append("g")
        .selectAll("line")
        .data(x.ticks())
        .join("line")
          .attr("x1", d => 0.5 + x(d))
          .attr("x2", d => 0.5 + x(d))
          .attr("y1", margin.top)
          .attr("y2", height - margin.bottom))
      .call(g => g.append("g")
        .selectAll("line")
        .data(y.ticks())
        .join("line")
          .attr("y1", d => 0.5 + y(d))
          .attr("y2", d => 0.5 + y(d))
          .attr("x1", margin.left)
          .attr("x2", width - margin.right));

    svg.append("g")
        .call(grid);

    const path = svg.append("g")
        .attr("fill", "none")
        .attr("stroke-width", 1.5)
        .attr("stroke-linejoin", "round")
        .attr("stroke-linecap", "round")
      .selectAll("path")
      .data(keys)
      .join("path")
        .attr("stroke", color)
        .style("mix-blend-mode", "multiply")
        .attr("d", key => line(data.filter(d => get_key(d) == key)));

    const by_key = key => data.filter(d => get_key(d) == key)

    function hover(svg, path) {
      if ("ontouchstart" in document) svg
          .style("-webkit-tap-highlight-color", "transparent")
          .on("touchmove", moved)
          .on("touchstart", entered)
          .on("touchend", left)
      else svg
          .on("mousemove", moved)
          .on("mouseenter", entered)
          .on("mouseleave", left);

      const dot = svg.append("g")
          .attr("display", "none");

      dot.append("circle")
          .attr("r", 2.5);

      dot.append("text")
          .attr("font-family", "sans-serif")
          .attr("font-size", 10)
          .attr("text-anchor", "middle")
          .attr("y", -8);

      function moved(event) {
        event.preventDefault();
        const pointer = d3.pointer(event, this);
        const xm = Math.round(x.invert(pointer[0]));
        const ym = y.invert(pointer[1]);
        const s = d3.least(keys, key => {
          const y_of = by_key(key).filter(d => get_x(d) == xm).map(get_y)
          if (y_of.length === 0) {
            return 9999999999999999;
          }
          return Math.abs(y_of[0] - ym)
          }
        );
        const d_of = by_key(s).filter(d => get_x(d) == xm)
        path.attr("stroke", d => d === s ? color(d) : "#ddd").filter(d => d === s).raise();
        if (d_of.length > 0) {
          const d = d_of[0]
          dot.attr("transform", `translate(${x(get_x(d))},${y(get_y(d))})`);
        }
        dot.select("text").text(s);
      }

      function entered() {
        path.style("mix-blend-mode", null).attr("stroke", "#ddd");
        dot.attr("display", null);
      }

      function left() {
        path.style("mix-blend-mode", "multiply").attr("stroke", color);
        dot.attr("display", "none");
      }
    }

    svg.call(hover, path);
  })
}

function barChart(sel, csv, get_x, get_y) {
  document.querySelector(sel).textContent = ""
  d3.csv(csv).then(data => {
    const margin = ({top: 30, right: 0, bottom: 30, left: 40})
    const width = 500
    const height = 200
    const color = "steelblue"

    const xAxis = g => g
      .attr("transform", `translate(0,${height - margin.bottom})`)
      .call(d3.axisBottom(x).tickFormat(i => get_x(data[i])).tickSizeOuter(0))

    const yAxis = g => g
      .attr("transform", `translate(${margin.left},0)`)
      .call(d3.axisLeft(y).ticks(null, data.format))
      .call(g => g.select(".domain").remove())
      .call(g => g.append("text")
          .attr("x", -margin.left)
          .attr("y", 10)
          .attr("fill", "currentColor")
          .attr("text-anchor", "start")
          .text(data.y))

    const x = d3.scaleBand()
      .domain(d3.range(data.length))
      .range([margin.left, width - margin.right])
      .padding(0.1)

    const y = d3.scaleLinear()
      .domain([0, d3.max(data, get_y)]).nice()
      .range([height - margin.bottom, margin.top])


    const svg = d3.select(sel).append("svg")
      .attr("width", width)
      .attr("height", height)
      .attr("viewBox", [0, 0, width, height]);

    svg.append("g")
        .attr("fill", color)
      .selectAll("rect")
      .data(data)
      .join("rect")
        .attr("x", (d, i) => x(i))
        .attr("y", d => y(get_y(d)))
        .attr("height", d => y(0) - y(get_y(d)))
        .attr("width", x.bandwidth())
      .append("title")
        .text(d => `${get_x(d)}: ${get_y(d)}`);

    svg.append("g")
        .call(xAxis);

    svg.append("g")
        .call(yAxis);

    const grid = g => g
      .attr("stroke", "currentColor")
      .attr("stroke-opacity", 0.1)
      .call(g => g.append("g")
        .selectAll("line")
        .data(y.ticks())
        .join("line")
          .attr("y1", d => 0.5 + y(d))
          .attr("y2", d => 0.5 + y(d))
          .attr("x1", margin.left)
          .attr("x2", width - margin.right));

    svg.append("g")
        .call(grid);

  })
}

function scatter(sel, csv, x_name, get_x, y_name, get_y) {
  document.querySelector(sel).textContent = ""
  d3.csv(csv).then(data => {
    const width = 600
    const height = 200
    const margin = ({top: 25, right: 20, bottom: 35, left: 40})

    const xAxis = g => g
      .attr("transform", `translate(0,${height - margin.bottom})`)
      .call(d3.axisBottom(x).ticks(width / 80))
      .call(g => g.select(".domain").remove())
      .call(g => g.append("text")
          .attr("x", width)
          .attr("y", margin.bottom - 4)
          .attr("fill", "currentColor")
          .attr("text-anchor", "end")
          .text(x_name))

    const yAxis = g => g
      .attr("transform", `translate(${margin.left},0)`)
      .call(d3.axisLeft(y))
      .call(g => g.select(".domain").remove())
      .call(g => g.append("text")
          .attr("x", -margin.left)
          .attr("y", 10)
          .attr("fill", "currentColor")
          .attr("text-anchor", "start")
          .text(y_name))

    const x = d3.scaleLinear()
      .domain(d3.extent(data, get_x)).nice()
      .range([margin.left, width - margin.right])

    const y = d3.scaleLinear()
      .domain(d3.extent(data, get_y)).nice()
      .range([height - margin.bottom, margin.top])

    const grid = g => g
      .attr("stroke", "currentColor")
      .attr("stroke-opacity", 0.1)
      .call(g => g.append("g")
        .selectAll("line")
        .data(x.ticks())
        .join("line")
          .attr("x1", d => 0.5 + x(d))
          .attr("x2", d => 0.5 + x(d))
          .attr("y1", margin.top)
          .attr("y2", height - margin.bottom))
      .call(g => g.append("g")
        .selectAll("line")
        .data(y.ticks())
        .join("line")
          .attr("y1", d => 0.5 + y(d))
          .attr("y2", d => 0.5 + y(d))
          .attr("x1", margin.left)
          .attr("x2", width - margin.right));

    const svg = d3.select(sel).append("svg")
      .attr("width", width)
      .attr("height", height)
      .attr("viewBox", [0, 0, width, height]);

    svg.append("g")
        .call(xAxis);

    svg.append("g")
        .call(yAxis);

    svg.append("g")
        .call(grid);

    svg.append("g")
        .attr("stroke", "steelblue")
        .attr("stroke-width", 1.5)
        .attr("fill", "none")
      .selectAll("circle")
      .data(data)
      .join("circle")
        .attr("cx", d => x(get_x(d)))
        .attr("cy", d => y(get_y(d)))
        .attr("r", 1);

//     svg.append("g")
//         .attr("font-family", "sans-serif")
//         .attr("font-size", 10)
//       .selectAll("text")
//       .data(data)
//       .join("text")
//         .attr("dy", "0.35em")
//         .attr("x", d => x(d.x) + 7)
//         .attr("y", d => y(d.y))
//         .text(d => d.name);

  })
}


function heatTable(sel, csv, get_xkey, get_ykey, get_value) {
  document.querySelector(sel).textContent = ""
  d3.csv(csv).then(data => {
    const margin = ({top: 20, right: 1, bottom: 40, left: 40})
    const width = 600
    const height = 16

    const xset = [...new Set(data.map(get_xkey))].sort()
    const yset = [...new Set(data.map(get_ykey))].sort()

    const innerHeight = height * yset.length

    const xAxis = g => g
      .call(g => g.append("g")
        .attr("transform", `translate(0,${margin.top})`)
        .call(d3.axisTop(x).ticks(null, "d"))
        .call(g => g.select(".domain").remove()))
      // .call(g => g.append("g")
      //   .attr("transform", `translate(0,${innerHeight + margin.top + 4})`)
      //   .call(d3.axisBottom(x)
      //       .tickValues(['hello' /* data.year */ ])
      //       .tickFormat(x => x)
      //       .tickSize(-innerHeight - 10))
      //   // .call(g => g.select(".tick text")
      //   //     .clone()
      //   //     .attr("dy", "2em")
      //   //     .style("font-weight", "bold")
      //       // .text("Measles vaccine introduced"))
      //   .call(g => g.select(".domain").remove()));

    const yAxis = g => g
      .attr("transform", `translate(${margin.left},0)`)
      .call(d3.axisLeft(y).tickSize(0))
      .call(g => g.select(".domain").remove())

    const color = d3.scaleSequentialSqrt([0, d3.max(data, get_value)], d3.interpolatePlasma)

    const x = d3.scaleBand()
      .domain(xset)
      .rangeRound([margin.left, width - margin.right])

    const y = d3.scaleBand()
      .domain(yset)
      .rangeRound([margin.top, margin.top + innerHeight])

    const svg = d3.select(sel).append("svg")
      .attr("width", width)
      .attr("height", height)
      .attr("viewBox", [0, 0, width, innerHeight + margin.top + margin.bottom])
      .attr("font-family", "sans-serif")
      .attr("font-size", 10);

    svg.append("g")
        .call(xAxis);

    svg.append("g")
        .call(yAxis);

    svg.append("g")
      .selectAll("g")
      .data(data)
      .join("rect")
        .attr("x", d => x(get_xkey(d)) + 1)
        .attr("y", d => y(get_ykey(d)) + 1)
        .attr("width", x.bandwidth() - 1)
        .attr("height", y.bandwidth() - 1)
        .attr("fill", d => color(get_value(d)))
      .append("title")
        .text((d, i) => `${get_ykey(d)} → ${get_xkey(d)} \n${get_value(d)}%`);
  })
}


