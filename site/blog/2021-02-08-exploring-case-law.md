---
layout: post
title: "Exploring Case Law"
date: 2021-02-08 00:14
comments: true
tags: law, data, visualization, scraping, analysis
---

<script src="https://unpkg.com/d3-sankey@0.12.3/dist/d3-sankey.min.js"></script>
<script src="https://d3js.org/d3.v6.min.js"></script>
<script src="/js/charts.js"></script>
<link rel="stylesheet" href="/css/law.css">


## Overview

In early 2021, spurred on by many discussions with my incredible, law-student
(among many other fantastic characteristics) girlfriend, I decided to try my
hand at analyzing Canada's legal system. Absolutely everything I know about the
law I've learned from TV shows and a year's worth of hanging out with law
students --- which is to say, I don't know anything.

Oh yeah, and also I don't know anything about data science or visualization. I'm
a computer scientist by trade, and can navigate my way around complicated
mathematics better than your average Joe. This projected seemed like a good
opportunity to teach myself some of the more obscure bits of graph theory,
interactive web design (most of the charts on this page are interactive,) data
scraping and subsequent mining.

Often, outsiders can bring new ideas and techniques to otherwise insular
communities. Despite knowing nothing, I managed to:

* determine the speed at which our court of appeal system works
* find that somewhere between 33% and 50% of all cases are completely trivial
  and could be easily automated away
* reliably find decisions that are important enough to have Wikipedia articles
* find the asymptotics of the growth rate of Canadian case law
* determine that BC and Alberta are by far the most powerful provinces with
    respect to the influence of their decisions, and,
* separate decisions automatically into 860 different "areas of law"

These are not half-bad results, if I do say so myself. And if one guy who doesn't
really know how to use this technology can do this well, imagine how much damage
someone with high-quality data, a budget, and knowledge could do. If you are in
the legal field and aren't yet positioning yourself for the upcoming automation
wave, maybe this essay will help convince you that the system isn't nearly as
robust to automation as you might think. I did all of this in two weeks, as an
outsider, with no domain knowledge. That should scare you.

Overall, I needed to collect and analyze all of the data myself. I spent maybe
fifteen hours programming things, and roughly 336 hours collecting data. I
fought with analytics tools for another ten hours, and this write-up took maybe
twenty hours. It was a fun project, but I'm happy to be done with it.


## Methodology

My assumption is that the citation graph of Canadian case law is sufficient to
find interesting data in the law. Unfortunately, this data doesn't seem to exist
in any convenient format. [CanLII][canlii] makes the data available on the web,
but doesn't provide any sort of downloadable database. So I needed to make my
own.

[canlii]: https://canlii.org

I wired up a small web-scraper that would connect to CanLII and crawl through
the millions of cases available there. My program loaded all the cases from the
Supreme Court and provincial courts of appeal, then followed every cited case.
And every case cited by every one of *those.* And so on and so forth, until
there were no more cited cases I hadn't yet downloaded.

After a few weeks of downloading, I was finished. In total, I downloaded 378,732
decisions from 269 different courts. Between these cases, there are 1,998,118
citations. Frighteningly, this is nowhere near the extent of Canadian case law;
it's maybe one tenth of the full corpus. But I feel comfortable in saying that
*this subset is the law as it exists today.* If a case doesn't lie anywhere in
the transitive dependencies of the Supreme Court or a court of appeals, it's not
contentious for anyone to care about.

Despite the large number of cases, it's important to discuss just how little
data I've got *per* case. The totality of my data about cases is of this form:

<figure>
<table>
<TR><TH>name</TH>
<TH>year</TH>
<TH>language</TH>
<TH>jurisdiction</TH>
<TH>court</TH>
</TR>
<TR><TD>Bamba c. R.</TD>
<TD>2019</TD>
<TD>fr</TD>
<TD>qc</TD>
<TD>qcca</TD>
</TR>
<TR><TD>R. v. Leach</TD>
<TD>2019</TD>
<TD>en</TD>
<TD>bc</TD>
<TD>bcca</TD>
</TR>
<TR><TD>R. v. Pruski</TD>
<TD>2006</TD>
<TD>en</TD>
<TD>on</TD>
<TD>oncj</TD>
</TR>
<TR><TD>Regina v. Imperial Optical Co. Ltd.</TD>
<TD>1972</TD>
<TD>en</TD>
<TD>on</TD>
<TD>oncj</TD>
</TR>
<TR><TD>Windheim c. Windheim</TD>
<TD>2012</TD>
<TD>en</TD>
<TD>qc</TD>
<TD>qcca</TD>
</TR>
</table>
<figcaption>decision data</figcaption>
</figure>

Notice that there is no information about the *contents* of these cases. I don't
know which judge was presiding, what was said, what the case was about,
keywords, or even who won.

In principle I could have extracted the involved parties by trying to tear apart
the name, but it seemed challenging to do well, and I don't think it would buy
me much information without knowing who won.

On the citation front, all I know is this:

<figure>
<table>
<TR><TH>citing_case</TH>
<TH>citing_year</TH>
<TH>cited_case</TH>
<TH>cited_year</TH>
</TR>
<TR><TD>The King v. Clark</TD>
<TD>1901</TD>
<TD>Automobile and Supply Co. v. Hands, Ltd.</TD>
<TD>1913</TD>
</TR>
<TR><TD>The King v. Clark</TD>
<TD>1901</TD>
<TD>The Queen v. Hammond</TD>
<TD>1898</TD>
</TR>
<TR><TD>The King v. Clark</TD>
<TD>1901</TD>
<TD>The Queen v. Harris</TD>
<TD>1898</TD>
</TR>
<TR><TD>Gallagher v. Hogg</TD>
<TD>1993</TD>
<TD>Katz v. Katz</TD>
<TD>1990</TD>
</TR>
<TR><TD>Gallagher v. Hogg</TD>
<TD>1993</TD>
<TD>Lagimodiere v. Lagimodiere</TD>
<TD>1991</TD>
</TR>
</table>
<figcaption>citation data</figcaption>
</figure>

Again, no *actual* information here.

To reiterate, there's nothing at all that we can use to learn what any
particular case was *about.* In this database, the vanishing majority of the
information available to us is which cases cite whom. Anything we want to figure
out needs to be inferred from that.


### Possible Issues

The Canadian legal system has existed much longer than the idea that information
should be freely available. While CanLII is an excellent source of data, it
explicitly states how complete its records are from each court. For example,
while CanLII has the entire corpus of Supreme Court decisions, it's only
maintained continuous coverage of the BC Court of Appeal (BCCA) since 1990. Other
courts have different starting dates for their continuous coverage.

This presents a systematic bias in our data, namely that more recent cases are
more readily available. To illustrate, the database contains 6,212 cases from the
BCCA before 1990, but 19,368 cases since. While we might be interested in
whether the volume of law is increasing over time, we must be careful to
restrict ourselves to the range of continuous coverage.

Looking only at citation data introduces another systematic bias in the dataset:
older cases have had a longer time to accumulate citations. Because we mainly
keep track of relationships between cases, it's possible for recent cases to
contradict previous decisions. Such a case is clearly very important to the law,
but will fly under our radar until it becomes commonly cited.


## Verifying the Dataset

Before getting started, let's make sure our data is sane. For example, since
case law is immutable, it's impossible for a case to cite a decision in the
future. Therefore we should never see any time-traveling citations in our
dataset.

But in fact, there are 1197 cases on CanLII which cite decisions in the future!
For example, [Molson v. Molson,
1998](https://www.canlii.org/en/ab/abqb/doc/1998/1998abqb476/1998abqb476.html)
cites [C.T.G. v R.R.G.,
2016](https://www.canlii.org/en/sk/skqb/doc/2016/2016skqb387/2016skqb387.html).
Clicking through the first link here shows that what is labeled as "Molson v.
Molson, 1998" is *actually* "Richardson v. Richardson, 2019."

A few other oddities show up, some of which are trial level courts citing their
appeal. These seem more reasonable, and I read this as *whoever was doing data
entry was typing in the wrong field.*

This erroneous data makes up only 0.31% of our dataset, so it doesn't seem like
fixing it is worth the effort.


## Average Age of Citation

How long do decisions stay relevant for? By looking at the average age at which
a decision is cited, we can get a feel.

<figure>
<div id="avg-duration">
select avg_age, count(*) from (select cast (avg(src_year - dst_year) as int) as avg_age from expanded_citations where src_year >= dst_year group by dst_hash) group by avg_age;

  <script>
    lineChart(
      "#avg-duration",
      "/data/1612727565.csv",
      "Avg Age of Decision when Cited",
      d => +parseInt(d.avg_age),
      "Decisions",
      d => +parseInt(d.count))
  </script>
</div>
<figcaption>Number of cases, by average age at time of citation</figcaption>
</figure>

It looks like cases stay relevant for about 11 years, at which point the
inflection point of this graph switches, and we see the long tail. This is for
the law in aggregate, but what about if we look at the average age when cited,
broken down by court?

<figure>
<div id="avg-duration-by-court">
select dst_court, cast (avg(src_year - dst_year) as int) as avg_age from expanded_citations where src_year >= dst_year and dst_court in (select court from important_courts order by max desc limit 15) group by dst_court;

  <script>
    barChart(
      "#avg-duration-by-court",
      "/data/1612746186.csv",
      d => d.dst_court,
      d => +parseInt(d.avg_age))
  </script>
</div>
<figcaption>Average age at time of citation, by court</figcaption>
</figure>

This chart shows the top 15 most important courts. Among them, the *really big,
important courts* hold sway longer than the smaller courts. But is the story
different for the smallest courts?

<figure>
<div id="avg-duration-by-smallest-court">
select dst_court, cast (avg(src_year - dst_year) as int) as avg_age from expanded_citations where src_year >= dst_year and dst_court in (select court from important_courts order by max asc limit 10) group by dst_court;

  <script>
    barChart(
      "#avg-duration-by-smallest-court",
      "/data/1612746614.csv",
      d => d.dst_court,
      d => +parseInt(d.avg_age))
  </script>
</div>
<figcaption>Average age at time of citation, by small court</figcaption>
</figure>

Definitely a different story here. These smaller courts' decisions fall off in
relevance significantly faster than their larger counterparts.

A corollary to this question of law relevance is to look *not at the citee, but
the citing case.* What is the average age of a case's citations?

<figure>
<div id="avg-age">
select avg_age, count(*) from (select cast (avg(src_year - dst_year) as int) as avg_age from expanded_citations where src_year >= dst_year group by src_hash) group by avg_age;

  <script>
    lineChart(
      "#avg-age",
      "/data/1612727606.csv",
      "Avg Age of Cited Decisions",
      d => +parseInt(d.avg_age),
      "Decisions",
      d => +parseInt(d.count))
  </script>
</div>
<figcaption>Number of cases, by average age of citation</figcaption>
</figure>

The fall-off here is closer to 20 years --- compared to the ten year average
lifespan of a decision. The discrepancy between these numbers suggests that
cases are likely to a few old cases and numerous newer ones. Maybe cases will
cite an original precedent, and then many other cases that have followed the
precedent?

When looking at average age of citation, we can look for trends over time. How
has the average age of citation changed over the years?

<figure>
<div id="avg-age-by-year">
select src_year, avg(avg_age) as avg_age from (select src_year, avg(src_year - dst_year) as avg_age from expanded_citations where src_year >= dst_year group by src_hash) group by src_year;

  <script>
    lineChart(
      "#avg-age-by-year",
      "/data/1612747472.csv",
      "Year",
      d => +parseInt(d.src_year),
      "Avg (Avg Age) of Cited Decisions",
      d => +parseFloat(d.avg_age).toFixed(2))
  </script>
</div>
<figcaption>Average average age of citation, by year</figcaption>
</figure>

And again, let's compare these average ages by big courts:

<figure>
<div id="avg-age-by-court">
select src_court, cast (avg(src_year - dst_year) as int) as avg_age from expanded_citations where src_year >= dst_year and src_court in (select court from important_courts order by max desc limit 15) group by src_court;

  <script>
    barChart(
      "#avg-age-by-court",
      "/data/1612747795.csv",
      d => d.src_court,
      d => +parseInt(d.avg_age))
  </script>
</div>
<figcaption>Average age of citation, by court</figcaption>
</figure>

Wow! Look at the big courts. There is almost no variance in the average age of
citations --- they're all clustered right around 13. Seeing as these are all of
the appeal-level courts, it strongly suggests that **this is the speed of our
legal system.** It takes thirteen years on average to make it through the entire
appeal process. Disgustingly slow.

There's nothing interesting in the small courts graph --- they show the same
variances as in the duration of case relevance.


## Complexity of the Law

Although there are nearly 400,000 cases in our dataset, I don't think most of
those can possibly be interesting. My understanding of case law is that usually
a precedent has already been set, and the judge almost always defers to that
precedent. To find cases like these, we can look at the number of decisions cited by
a case. If a case cites only a few decisions (let's say three or fewer,) it's
probably just agreeing with precedent.

<figure>
<div id="complexity">
select c, count(*) as count from (select count(*) as c from expanded_citations where src_year >= (select year from coverage where court = src_court) group by src_hash) group by c;
BUCKETED BY HAND

  <script>
    pieChart(
      "#complexity",
      "/data/1612748474.csv",
      // "Citation Count",
      d => d.c,
      // "Cases",
      d => +parseInt(d.count))
  </script>
</div>
<figcaption>Cases by number of decisions cited</figcaption>
</figure>

The number of cases cited falls off exponentially as we'd expect, so I bucketed
the higher number of citations in this chart. But take a look: roughly one third
of all cases cite three or fewer decisions, and nearly a sixth cite *only one!*

If our hypothesis is true, it means that one sixth of all cases are glaringly
obvious wastes of time, and a third are trivially decided. But does this hold
true across all courts? Let's look at the breakdown for a few of the highest
importance courts:

<figure>
<div id="complexity-scc">
select c, count(*) as count from (select count(*) as c from expanded_citations where src_year >= (select year from coverage where court = src_court) and src_year >= 1950 and src_court = 'scc' group by src_hash) group by c;

  <script>
    pieChart(
      "#complexity-scc",
      "/data/1612750035.csv",
      // "Citation Count",
      d => d.c,
      // "Cases",
      d => +parseInt(d.count))
  </script>
</div>
<figcaption>Cases by number of decisions cited (SCC, 1950+)</figcaption>
</figure>

I filtered the SCC decisions to only look at cases after 1950 --- earlier ones
were too likely to not have their citations available on CanLII, and would thus
throw off our analysis. But amazingly, even of cases that make it to the Supreme
Court, still more than a third of them cite only three or fewer decisions.

That sounds a little crazy to me, so I went on CanLII and randomly clicked on a
few supreme court cases. And sure enough, many of them *do* only cite one case!
Inspecting them visually, these cases come with extraordinarily short documents
--- many are under 1000 words.

Let's see if this holds for the AB, BC, ON and QC courts of appeal as well:

<figure>
<div id="complexity-abca">
select c, count(*) as count from (select count(*) as c from expanded_citations where src_year >= (select year from coverage where court = src_court) and src_court = 'abca' group by src_hash) group by c;

  <script>
    pieChart(
      "#complexity-abca",
      "/data/1612750541.csv",
      // "Citation Count",
      d => d.c,
      // "Cases",
      d => +parseInt(d.count))
  </script>
</div>
<figcaption>Cases by number of decisions cited (ABCA)</figcaption>
</figure>

<figure>
<div id="complexity-bcca">
select c, count(*) as count from (select count(*) as c from expanded_citations where src_year >= (select year from coverage where court = src_court) and src_court = 'bcca' group by src_hash) group by c;

  <script>
    pieChart(
      "#complexity-bcca",
      "/data/1612750650.csv",
      // "Citation Count",
      d => d.c,
      // "Cases",
      d => +parseInt(d.count))
  </script>
</div>
<figcaption>Cases by number of decisions cited (BCCA)</figcaption>
</figure>

<figure>
<div id="complexity-onca">
select c, count(*) as count from (select count(*) as c from expanded_citations where src_year >= (select year from coverage where court = src_court) and src_court = 'onca' group by src_hash) group by c;

  <script>
    pieChart(
      "#complexity-onca",
      "/data/1612750834.csv",
      // "Citation Count",
      d => d.c,
      // "Cases",
      d => +parseInt(d.count))
  </script>
</div>
<figcaption>Cases by number of decisions cited (ONCA)</figcaption>
</figure>

<figure>
<div id="complexity-qcca">
select c, count(*) as count from (select count(*) as c from expanded_citations where src_year >= (select year from coverage where court = src_court) and src_court = 'qcca' group by src_hash) group by c;

  <script>
    pieChart(
      "#complexity-qcca",
      "/data/1612750959.csv",
      // "Citation Count",
      d => d.c,
      // "Cases",
      d => +parseInt(d.count))
  </script>
</div>
<figcaption>Cases by number of decisions cited (QCCA)</figcaption>
</figure>

Pretty close to *half* of the cases that come through these appeal-level courts
are trivial. If we could automate decisions of this sort, we should be able to
make the appeal system roughly 70% faster --- reducing the average time per case
from 13 years to 7.5. I can't find any numbers on how expensive the court system
is to run, but this would reduce its cost by 70% as well, which is almost
certainly something worth investigating.


## Volume of Law

What's the rate of law being accumulated? Is it accelerating? We can look at the
number of cases per year per court over the last 30 years[^not-all-time] to get a sense of the
acceleration of accumulation:

[^not-all-time]: Due to the differing dates of continuing coverage, we
  unfortunately can't look at this metric over the history of Canadian law.

<figure>
<div id="volume">
  select court, year, count(*) as count from decisions d where court in (select court from important_courts order by max desc limit 10) and year >= 1990 and year >= (select year from coverage c where d.court = c.court) and 2021 > year group by court, year;

  <script>
    multiLineChart(
      "#volume",
      "/data/1612761383.csv",
      d => d.court,
      d => +parseInt(d.year),
      d => +parseInt(d.count))
  </script>
</div>
<figcaption>Volume of decisions by top courts, starting after dates of continuing coverage</figcaption>
</figure>

Those lines all look pretty constant to me, which makes sense if you assume the
courts are limited by time and that they have no gains in efficiency (lol.) So
no, the volume at which law is accumulating in Canada is not accelerating. But
remember that this graph is the velocity of change, which means the volume of
law is growing linearly with respect to time.

<figure>
<div id="total-volume">
select y.year, count(*) as volume from (select distinct year from decisions order by year) y inner join decisions d on y.year >= d.year where 2021 > y.year group by y.year;

  <script>
    lineChart(
      "#total-volume",
      "/data/1612762714.csv",
      "Year",
      d => +parseInt(d.year),
      "Volume of Law",
      d => +parseInt(d.volume))
  </script>
</div>
<figcaption>Number of cases in existence, by year</figcaption>
</figure>

No, wait, that *does* look exponential. I forgot. While the volume *per court*
is staying constant, the number *of courts* grows with year:

<figure>
<div id="total-volume-courts">
select y.year, count(*) as volume from (select distinct year from decisions order by year) y inner join (select min(year) as year from decisions group by court) c on y.year >= c.year where 2021 > y.year group by y.year;

  <script>
    lineChart(
      "#total-volume-courts",
      "/data/1612762752.csv",
      "Year",
      d => +parseInt(d.year),
      "Number of Courts",
      d => +parseInt(d.volume))
  </script>
</div>
<figcaption>Number of courts in existence, by year</figcaption>
</figure>

This graph estimates the number of courts in existence by the first decision we
have from that court being the year it was created --- which seems like a
satisfactory proxy. The curve appears to have leveled off, but I think this is
due to 2020 being a GLOBAL PANDEMIC. If I had to guess, I'd say the inflection
point around 1997 is an artifact of the digitization of law, and that this curve
will continue linearly.


## Who Cites Whom?

Are certain provinces "friends?" Which provinces influence which others? Let's
look at the percentage by which one provinces' courts cite another provinces:

<figure>
<div id="juris-cite-juris">
with data as (select src_jurisdiction, dst_jurisdiction, count(*) as count from expanded_citations where src_jurisdiction != dst_jurisdiction group by src_jurisdiction, dst_jurisdiction), totals as (select src_jurisdiction, sum(count) as total from data group by src_jurisdiction) select d.src_jurisdiction, d.dst_jurisdiction, d.count * 100.0 / t.total as count from data d inner join totals t on d.src_jurisdiction = t.src_jurisdiction;

  <script>
    heatTable(
      "#juris-cite-juris",
      "/data/1612768242.csv",
      d => d.dst_jurisdiction,
      d => d.src_jurisdiction,
      d => +parseFloat(d.count).toFixed(2))
  </script>
</div>
<figcaption>Citing jurisdiction (left) by cited jurisdiction (top), in percent.
Blue is less often.</figcaption>
</figure>

Yow! The fed is understandably white hot, and dominates this chart. Let's remove
it to look more closely at the provinces:

<figure>
<div id="juris-cite-juris-no-ca">
with data as (select src_jurisdiction, dst_jurisdiction, count(*) as count from expanded_citations where src_jurisdiction != dst_jurisdiction and src_jurisdiction != 'ca' and dst_jurisdiction != 'ca' group by src_jurisdiction, dst_jurisdiction), totals as (select src_jurisdiction, sum(count) as total from data group by src_jurisdiction) select d.src_jurisdiction, d.dst_jurisdiction, d.count * 100.0 / t.total as count from data d inner join totals t on d.src_jurisdiction = t.src_jurisdiction;

  <script>
    heatTable(
      "#juris-cite-juris-no-ca",
      "/data/1612769065.csv",
      d => d.dst_jurisdiction,
      d => d.src_jurisdiction,
      d => +parseFloat(d.count).toFixed(2))
  </script>
</div>
<figcaption>Citing jurisdiction (left) by cited jurisdiction (top), in percent.
Blue is less often.</figcaption>
</figure>

Now Ontario dominates, followed closely by BC and Alberta. Nobody cites the
territories --- but also, nobody cites Quebec. No wonder they feel discriminated
against.

Let's look at the same chart, but this time split by big courts rather than
provinces.

<figure>
<div id="court-cite-court">
with courts as (select court from important_courts order by max desc limit 13), data as (select src_court, dst_court, count(*) as count from expanded_citations where src_court != dst_court and src_court in courts and dst_court in courts group by src_court, dst_court), totals as (select src_court, sum(count) as total from data group by src_court) select d.src_court, d.dst_court, d.count * 100.0 / t.total as count from data d inner join totals t on d.src_court = t.src_court;

  <script>
    heatTable(
      "#court-cite-court",
      "/data/1612769747.csv",
      d => d.dst_court,
      d => d.src_court,
      d => +parseFloat(d.count).toFixed(2))
  </script>
</div>
<figcaption>Citing court (left) by cited court (top), in percent.
Blue is less often.</figcaption>
</figure>

There's an interesting feature of this graph, namely the "friendship pairs" that
lie along the diagonal. For example, `bcsc` cites `bcca` much more than it cites
anything but the `scc` --- and vice versa! Thinking about it, I guess this makes
sense, and is mainly showing us the hierarchical nature of such courts. Of
course `bcsc` cites `bcca` more than chance, since it must defer. And vice versa
also makes sense, because a case must go through `bcsc` in order to get to
`bcca`.

Well, not every stream you pan will have gold.


## Determining Important Cases

The sheer size of the case law corpus is staggering. My dataset contains roughly
400,000 decisions --- a small fraction of the *actual law.* And this is a few
orders of magnitude larger than any human could possibly remember.

Thankfully, most of this data is noise. Most cases taken to court are decided
uninterestingly: the presiding judge simply defers to precedent and everyone
goes on their way. It's safe to say that decisions of this sort are unimportant.
In my opinion, the desired end-state of the law is for all cases to be decided
like this --- at that point, we've got a stable, entirely-predictable system.

But that is not (yet!) the world we live in. Some cases *are* interesting ---
for example, the ones which *set* precedent, and the ones which *contradict*
precedent. How can we find these cases?

Humans would probably look at the cases, and think about first principles, and
talk to other people they think are smart, and think really hard, and maybe go
consult some textbooks, in an attempt to determine which cases are important.
The computer is too dumb to do any of that. It's only good at moving numbers
around ridiculous fast, and I'm very good at turning problems that don't sound
like they involve numbers into ones that do.

So how can we introduce numbers into this problem?

Rather than trying to compute importance directly, let's instead try to
approximate it. Intuitively, cases which are important will be cited more often
than cases which are not important. Thus, citation count is --- to a first
approximation --- a good model for importance. Indeed, this seems to be how most
[law software](https://www.lexisnexis.com/ln-media/totg/p/lotg.aspx?mediaid=121105)
computes importance.

To improve our model, let's take an intellectual detour and think about the
importance of websites. Imagine the website for Reputable News Network (RNN). By
virtue of being a reputable news site, it will naturally be linked to quite
often. Like in the case law example, this should improve our estimate of RNN
being an important site.

But now consider *the sites that RNN links to.* Maybe RNN is running a story on
bloggers, and links to Paul Podunk's Personal Page (PPPP). PPPP is news-worthy by
definition due to being on RNN, and surely news-worthy things are more
important than non-influential things. Thus, PPPP should be considered more
important, sheerly by virtue of having been linked-to by an important thing.

Of course, this new influence that PPPP has acquired from RNN should also be
accounted for --- sites that PPPP links to become more important due to their
relevance to PPPP. And so on, and so forth. But critically, these sites are
considered *less* important than they would be if RNN linked to them directly,
since RNN is significantly more influential than PPPP.

The key assumption of this model is that important things run in the same
circles as other important things. This jives with my intuition. It's clearly
true in the news cycle. It's why people name drop in order to raise their social
standing --- if they know important people, they must too be important. Of
course, this is not a perfect model for importance, but it gets the broad
strokes.

And, if you have any remaining doubts, this exact algorithm is what powers
Google search. Clearly, Google (an important entity) wouldn't be using this
technique if it didn't work. Therefore it probably does work. See? This
technique works *everywhere.*

Returning to law, let's replace "websites" with "decisions," and "links" with
"citations." We can compute the importance of cases by seeing which important
cases they're connected to.


### Verifying Important Cases

After crunching the numbers for a few hours, I came up with an *importance
score* for each case. It's hard to get a real intuition for [what these scores
*are*][evc], but a safe interpretation is that a higher importance score
corresponds to a more-important case.

[evc]: https://en.wikipedia.org/wiki/Eigenvector_centrality

To verify that these importance scores actually correspond with reality, I took
the names and years of the top 50 cases, and searched for a Wikipedia page on
the topic. My theory is that *really* important cases will be important enough
to have Wikipedia commentary about them for laypeople like me.

At time of writing, of the top 50 cases, 34 have Wikipedia articles. And among
those, 22 are described in the first sentence as either a "landmark" or a
"leading" case.[^previous] That's a pretty good sign.

[^previous]: In a pre-print of this essay that contained only half of the
  dataset, 42 of the top 50 had Wikipedia articles. Of these cases, 31 were
  "leading" or "landmark." It's not clear to me why this metric degraded when
  adding more data, except possibly that the inclusion of more cases has brought
  out connections that are harder for humans to keep track of. I'm very
  confident in the math here.

Without further ado, here are the 50 most important cases by my analysis:

<ol>
<li><a href="https://en.wikipedia.org/wiki/Dunsmuir_v_New_Brunswick">Dunsmuir v. New Brunswick</a></li>
<li><a href="https://en.wikipedia.org/wiki/Canada_(Minister_of_Citizenship_and_Immigration)_v_Khosa">Canada (Citizenship and Immigration) v. Khosa</a></li>
<li><a href="https://en.wikipedia.org/wiki/Baker_v_Canada_(Minister_of_Citizenship_and_Immigration)">Baker v. Canada (Minister of Citizenship and Immigration)</a></li>
<li><a href="https://en.wikipedia.org/wiki/Dunsmuir_v_New_Brunswick">Newfoundland and Labrador Nurses' Union v. Newfoundland and Labrador (Treasury Board)</a></li>
<li>Housen v. Nikolaisen, 2002</li>
<li><a href="https://en.wikipedia.org/wiki/Hunter_v_Southam_Inc">Hunter et al. v. Southam Inc.</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Collins_(1987)">R. v. Collins</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Oakes">R. v. Oakes</a></li>
<li>Alberta (Information and Privacy Commissioner) v. Alberta Teachers' Association, 2011</li>
<li><a href="https://en.wikipedia.org/wiki/Pushpanathan_v_Canada_(Minister_of_Citizenship_and_Immigration)">Pushpanathan v. Canada (Minister of Citizenship and Immigration)</a></li>
<li><a href="https://en.wikipedia.org/wiki/Re_Rizzo_%26_Rizzo_Shoes_Ltd">Rizzo & Rizzo Shoes Ltd. (Re)</a></li>
<li><a href="https://en.wikipedia.org/wiki/Dr_Q_v_College_of_Physicians_and_Surgeons_of_British_Columbia">Dr. Q. v. College of Physicians and Surgeons of British Columbia</a></li>
<li><a href="https://en.wikipedia.org/wiki/Canada_(Director_of_Investigation_and_Research)_v_Southam_Inc">Canada (Director of Investigation and Research) v. Southam Inc.</a></li>
<li><a href="https://en.wikipedia.org/wiki/Law_Society_of_New_Brunswick_v_Ryan">Law Society of New Brunswick v. Ryan</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Big_M_Drug_Mart_Ltd">R. v. Big M Drug Mart Ltd.</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Grant">R. v. Grant</a></li>
<li><a href="https://en.wikipedia.org/wiki/Reference_Re_BC_Motor_Vehicle_Act">Re B.C. Motor Vehicle Act</a></li>
<li>Agraira v. Canada (Public Safety and Emergency Preparedness), 2013</li>
<li><a href="https://en.wikipedia.org/wiki/Canadian_Union_of_Public_Employees_v_Ontario_(Minister_of_Labour)">C.U.P.E. v. Ontario (Minister of Labour)</a></li>
<li><a href="https://en.wikipedia.org/wiki/Suresh_v_Canada_(Minister_of_Citizenship_and_Immigration)">Suresh v. Canada (Minister of Citizenship and Immigration)</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Stillman">R. v. Stillman</a></li>
<li>R. v. M. (C.A.), 1996</li>
<li><a href="https://en.wikipedia.org/wiki/R_v_O%27Connor">R. v. O'Connor</a></li>
<li>Toronto (City) v. C.U.P.E., Local 79, 2003</li>
<li><a href="https://en.wikipedia.org/wiki/Andrews_v_Law_Society_of_British_Columbia">Andrews v. Law Society of British Columbia</a></li>
<li><a href="https://en.wikipedia.org/wiki/Irwin_Toy_Ltd_v_Quebec_(AG)">Irwin Toy Ltd. v. Quebec (Attorney General)</a></li>
<li><a href="https://en.wikipedia.org/wiki/Canada_(AG)_v_Mossop">Canada (Attorney General) v. Mossop</a></li>
<li>Bell ExpressVu Limited Partnership v. Rex, 2002</li>
<li><a href="https://en.wikipedia.org/wiki/Canada_(Minister_of_Citizenship_and_Immigration)_v_Vavilov">Canada (Minister of Citizenship and Immigration) v. Vavilov</a></li>
<li><a href="https://en.wikipedia.org/wiki/Canadian_Union_of_Public_Employees,_Local_963_v_New_Brunswick_Liquor_Corp">C.U.P.E. v. N.B. Liquor Corporation</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Edwards_Books_and_Art_Ltd">R. v. Edwards Books and Art Ltd.</a></li>
<li>R. v. Lyons, 1987</li>
<li>McLean v. British Columbia (Securities Commission), 2013</li>
<li><a href="https://en.wikipedia.org/wiki/Union_des_Employes_de_Service,_Local_298_v_Bibeault">U.E.S., Local 298 v. Bibeault</a></li>
<li>Canada (Canadian Human Rights Commission) v. Canada (Attorney General), 2011</li>
<li>R. v. Garofoli, 1990</li>
<li><a href="https://en.wikipedia.org/wiki/Blencoe_v_British_Columbia_(Human_Rights_Commission)">Blencoe v. British Columbia (Human Rights Commission)</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Therens">R. v. Therens</a></li>
<li>Smith v. Alliance Pipeline Ltd., 2011</li>
<li><a href="https://en.wikipedia.org/wiki/R_v_W_(D)">R. v. W.(D.)</a></li>
<li><a href="https://en.wikipedia.org/wiki/RJR-MacDonald_Inc_v_Canada_(AG)">RJR-MacDonald Inc. v. Canada (Attorney General)</a></li>
<li>Sketchley v. Canada (Attorney General), 2005</li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Mann">R. v. Mann</a></li>
<li>Cepeda-Gutierrez v. Canada (Minister of Citizenship and Immigration), 1998</li>
<li><a href="https://en.wikipedia.org/wiki/Slaight_Communications_Inc_v_Davidson">Slaight Communications Inc. v. Davidson</a></li>
<li>Committee for Justice and Liberty et al. v. National Energy Board et al., 1976</li>
<li>R. v. Debot, 1989</li>
<li>Mission Institution v. Khela, 2014</li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Morgentaler">R. v. Morgentaler</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Sharpe">R. v. Sharpe</a></li>
</ol>

If you're a law professional, you might disagree with this list. Maybe the
ordering is wrong. Maybe there are some glaring omissions, or some strange
choices. Glaring omissions are probably caused by recency bias --- new important
decisions simply haven't had time to accumulate citations (and thus importance.)
The wrong ordering? That's just like, your opinion, man.

But of particular interest to me are the cases on this list that *aren't on
Wikipedia.* Assuming Wikipedia is a reasonable proxy for what lawyers think are
important cases, the missing articles here have previously-unacknowledged
importance.

Anyway, it seems like my calculated importance score correlates pretty well with
real-world importance. But let's try to falsify that hypothesis, and see if the
bottom-ranked cases have Wikipedia articles.

I checked. They don't. Not a single hit in the 50 I tried[^try-more]. I also
checked for Wikipedia articles on a randomly-selected set of 50 cases, in an
attempt to find the base-rate we should expect to see. Again, there wasn't a
single hit.

[^try-more]: I'd like to have checked a few thousand, but this is a very manual
  process.

These negative results add strong evidence that my importance score is
*measuring something real.* Remember, there is absolutely no human judgment
going into this analysis; *my program is simply crunching the numbers based on
who cites whom.* The fact that it can identify *any* important cases whatsoever is
jaw-dropping.


### Statistical Biases

So we've successfully found important cases. My first question is, how necessary
was all of this fancy math? Could I just have ignored it and gone straight to
number of citations? How correlated is the importance metric with the raw number
of citations? Let's see:

<figure>
<div id="correlation">
select dst_importance, count(*) as count from expanded_citations group by dst_hash order by dst_importance desc limit 1000 offset 1;

  <script>
    scatter(
      "#correlation",
      "/data/1612759421.csv",
      "Importance",
      d => parseFloat(d.dst_importance).toFixed(5),
      "Citation Count",
      d => +d.count)
  </script>
</div>
<figcaption>Correlation between the importance metric and the number of times
cited.</figcaption>
</figure>

If the two metrics were strongly correlated, we should see a nice sharp diagonal
line going up and to the right. We don't. Instead we see, well, I'll leave the
Rorschach test up to you. There's clearly some correlation, but it's not
particularly strong. So no --- we can't just use the citation count!

Another thing you might be wondering is, "what courts do all these important
cases come from?" Good question:

<figure>
<div id="court-of-important-cases">
select court, count(*) as count from (select court from decisions order by importance desc limit 1000) x group by court having count > 20;
THEN OTHER = 1000 -

  <script>
    pieChart(
      "#court-of-important-cases",
      "/data/1612753367.csv",
      d => d.court,
      d => d.count)
  </script>
</div>
<figcaption>Courts of the top 1000 important cases</figcaption>
</figure>

Interesting. The Supreme Court takes most of the cake, but Ontario and Quebec
are crowded out by BC and Alberta. Drilling down into the "other" category from the chart above:

<figure>
<div id="court-of-other-cases">
select court, count(*) as count from (select court from decisions order by importance desc limit 1000) x group by court having count <= 20 and count > 5;

  <script>
    pieChart(
      "#court-of-other-cases",
      "/data/1612753494.csv",
      d => d.court,
      d => d.count)
  </script>
</div>
<figcaption>Drilling down on the "other" category</figcaption>
</figure>

It surprising to me that Ontario and Quebec are so underrepresented in their
number of important cases, compared to their populations and age. I don't know
what's going on here --- please let me know if you do, gentle reader.


The other big question I have is to what degree this importance factor is biased
by the courts' continuous coverage. That is to say, of the most important cases
identified, how many of them are from before CanLII started continuous coverage?

<!--
select count(*) as count, c.year from decisions d inner join coverage c on d.court = c.court where d.hash in (select hash from decisions where court != 'scc' order by importance desc limit 1000) and d.year < c.year;
-->

Only 13 of the top 1000 (1.3%) cases are from before the year of continuous
coverage. This doesn't jive with my intuition --- presumably the cases which are
on CanLII before the date of continuous coverage *are the most important ones.*
They're the cases that someone went in and added manually, before the system was
set up to track this stuff automatically.

OK, so the importance metric is clearly biased against old cases. But is it also
biased against *new* cases? Let's look at the number of top important cases by
year:

<figure>
<div id="new-bias">
select year, count(*) as count from decisions where hash in (select hash from decisions order by importance desc limit 1000) group by year;

  <script>
    lineChart(
      "#new-bias",
      "/data/1612754087.csv",
      "Year",
      d => +parseInt(d.year),
      "Number of Important Cases",
      d => +parseInt(d.count))
  </script>
</div>
<figcaption>Number of top 1000 important cases, by year</figcaption>
</figure>

Rather surprisingly, it doesn't seem to be. I'd expect newer cases to not have
had time to accumulate citations, and to thus be biased-against in the
importance metric. So what's going on here? It's that I slightly lied to you
earlier; that our importance metric doesn't take into account the direction of
the citation. In essence, it means that you get the same amount of influence for
citing important cases as you would for important cases citing you. This is
often a better approach than the directed version for datasets in which there
are no loops. In the absence of loops (where X cites Y which cites Z which cites
X again,) all of the influence gets pooled at the very oldest cases, and in
effect tracks progeny.

Switching to this directed importance metric will likely show the bias against
recency that we'd expect to see. So let's look at that same chart as before,
except using the directed importance metric instead:

<figure>
<div id="dimportance">
select year, count(*) as count from decisions where hash in (select hash from decisions order by dimportance desc limit 1000) group by year;

  <script>
    lineChart(
      "#dimportance",
      "/data/1612754125.csv",
      "Year",
      d => +parseInt(d.year),
      "Number of Important Cases",
      d => +parseInt(d.count))
  </script>
</div>
<figcaption>Number of top 1000 important cases with the directed importance
metric, by year</figcaption>
</figure>

<!-- TODO(sandy): add support for missing data to lineChart -->

This metric nicely prioritizes old cases, like our previous metric emphasized
newer cases. In fact, the directed importance score puts 865 of the its top 1000
(86.5%) cases before the date of continuous coverage.

We'd be very happy if we could somehow mix the two metrics together to get an
importance score that has no time-bias. Unfortunately, it's unclear to me how to
combine the two together; we probably can't meaningfully add eigenvalues --- but
let's try it anyway.

<figure>
<div id="both-importance">
select year, count(*) as count from decisions where hash in (select hash from decisions order by importance + dimportance desc limit 1000) group by year;

  <script>
    lineChart(
      "#both-importance",
      "/data/1612754230.csv",
      "Year",
      d => +parseInt(d.year),
      "Number of Important Cases",
      d => +parseInt(d.count))
  </script>
</div>
<figcaption>Number of top 1000 important cases with the sum importance metric,
by year</figcaption>
</figure>

I don't know if this is meaningful. It seems unlikely that there was a period of
40 years from 1940 to 1980 in which no important decisions were made --- but
then I realized this corresponds pretty closely when with Canada became a
Commonwealth nation (1931) and when it became sovereign (1982). To quote the
[first link on Google I found][history]:

[history]: https://www.history.com/news/canada-independence-from-britain-france-war-of-1812

> In 1931, England put Canada on equal footing with other Commonwealth countries
> through the Statute of Westminster, which essentially gave its dominions full
> legal freedom and equal standing with England and one another. However,
> Britain still had the ability to amend the Canadian constitution, and **Canada
> took time to cut its legal ties to England**. Meanwhile, it adopted its own
> national symbols, like the Canadian flag, featuring the maple leaf, which
> debuted in 1965.
>
> It took five decades after the Statute of Westminster for Canada to make its
> final step toward full sovereignty. In 1982, it adopted its own constitution
> and became a completely independent country.

Emphasis mine. Maybe this "taking its time" stuff was just Canada coasting?
Hopefully the law and/or history people can get in touch and let me know if this
graph of mine is at all meaningful. This is flaw in the data-driven approach ---
your analysis can only be as good as your data is. We're always going to need
subject matter experts.


## Discovering Neighborhoods

Imagine I give you a map of the world's road network, with all of the
topological features like water and altitude removed, as well as all landmarks
and zoning information. For example:

<img src="/images/law/city.png" style="width: 100%">

There are two cities on this map. It's not very hard to spot them, is it? The
cities are exceptionally dense networks of roads, compared to the relatively
spare highways that connect them.

Interestingly, this same phenomenon occurs within cities:

<img src="/images/law/neighborhood.png" style="width: 100%">

It's easy to find downtown on this map, and if you pay attention to what are
obviously bridges, you can find the smaller cities that make up the big
metropolitan area. Again, the trick is to identify areas that have tightly woven
intra-road networks, but relatively sparse interconnections.

We can use this same trick to identify "neighborhoods" of law --- that is,
clusters of cases that commonly cite one another, but which rarely cite other
neighborhoods. [Our algorithm][louvain] starts by putting every case in its own (very
lonely) community, and then merging communities which are more interconnected
than should be expected by random.

[louvain]: https://en.wikipedia.org/wiki/Louvain_method

After crunching the numbers, the five most important decisions in each of our
three most important, highly-populated communities are:

### Community 249
<ul>
<li><a href="https://canlii.org/en/ca/scc/doc/2008/2008scc9/2008scc9.html">Dunsmuir v. New Brunswick</a></li>
<li><a href="https://canlii.org/en/ca/scc/doc/2009/2009scc12/2009scc12.html">Canada (Citizenship and Immigration) v. Khosa</a></li>
<li><a href="https://canlii.org/en/ca/scc/doc/1999/1999canlii699/1999canlii699.html">Baker v. Canada (Minister of Citizenship and Immigration)</a></li>
<li><a href="https://canlii.org/en/ca/scc/doc/2011/2011scc62/2011scc62.html">Newfoundland and Labrador Nurses' Union v. Newfoundland and Labrador (Treasury Board)</a></li>
<li><a href="https://canlii.org/en/ca/scc/doc/2011/2011scc61/2011scc61.html">Alberta (Information and Privacy Commissioner) v. Alberta Teachers'Association</a></li>
</ul>

In order to try and figure out what community this is (249 isn't a *great*
name[^naming-things]), I clicked on each CanLII link and read (with my *eyes,*
like a *peasant*) the tags that whoever filed these cases wrote down. They are:

[^naming-things]: "There are only two hard things in Computer Science: cache invalidation and naming things." --Phil Karlton

* Administrative law -- Procedural fairness
* Administrative law -- Review of discretion -- Approach to review of discretionary decision making.
* Administrative law -- Judicial review -- Implied decision
* Administrative law -- Judicial review -- Standard of review
* Administrative law -- Natural justice -- Procedural fairness
* Administrative law -- Role and adequacy of reasons -- Procedural fairness
* Administrative law -- Standard of review
* Courts -- Appellate review

Looks like community 249 is really some sort of administrative review of law.

Remember, I only looked at these tags in order to try to give a
human-appropriate name to community 249. The computer didn't have access to
these tags when it was discovering it; it was merely looking at where the roads
are dense.


### Community 527
<ul>
<li><a href="https://canlii.org/en/ca/scc/doc/1986/1986canlii46/1986canlii46.html">R. v. Oakes</a></li>
<li><a href="https://canlii.org/en/ca/scc/doc/1985/1985canlii69/1985canlii69.html">R. v. Big M Drug Mart Ltd.</a></li>
<li><a href="https://canlii.org/en/ca/scc/doc/1985/1985canlii81/1985canlii81.html">Re B.C. Motor Vehicle Act</a></li>
<li><a href="https://canlii.org/en/ca/scc/doc/1989/1989canlii2/1989canlii2.html">Andrews v. Law Society of British Columbia</a></li>
<li><a href="https://canlii.org/en/ca/scc/doc/1989/1989canlii87/1989canlii87.html">Irwin Toy Ltd. v. Quebec (Attorney General)</a></li>
</ul>

The tags here are:

* Constitutional law -- Canadian Charter of Rights and Freedoms
* Constitutional law -- Charter of Rights -- Application
* Constitutional law -- Charter of Rights -- Freedom of expression
* Constitutional law -- Charter of Rights -- Fundamental justice
* Constitutional law -- Charter of Rights -- Presumption of innocence
* Constitutional law -- Charter of Rights -- Reasonable limits

Seems pretty cut and dried. "Charter of Rights."

### Community 192
<ul>
<li><a href="https://canlii.org/en/ca/scc/doc/1984/1984canlii33/1984canlii33.html">Hunter et al. v. Southam Inc.</a></li>
<li><a href="https://canlii.org/en/ca/scc/doc/1987/1987canlii84/1987canlii84.html">R. v. Collins</a></li>
<li><a href="https://canlii.org/en/ca/scc/doc/2009/2009scc32/2009scc32.html">R. v. Grant</a></li>
<li><a href="https://canlii.org/en/ca/scc/doc/1997/1997canlii384/1997canlii384.html">R. v. Stillman</a></li>
<li><a href="https://canlii.org/en/ca/scc/doc/1990/1990canlii52/1990canlii52.html">R. v. Garofoli</a></li>
</ul>

With tags:

* Constitutional law -- Canadian Charter of Rights and Freedoms -- Unreasonable search and seizure
* Constitutional law -- Charter of Rights -- Admissibility of evidence
* Constitutional law -- Charter of Rights -- Arbitrary detention
* Constitutional law -- Charter of Rights -- Enforcement — Exclusion of evidence
* Constitutional law -- Charter of Rights -- Search and seizure
* Constitutional law -- Charter of Rights -- Security of person
* Constitutional law -- Charter of Rights -- Unreasonable search and seizure
* Criminal law -- Interception of private communications -- Access to sealed packet -- Validity of wiretap authorizations
* Criminal law -- Interception of private communications -- Admissibility of evidence
* Criminal law -- Power of search incidental to arrest

This one is very clearly on the police being naughty and doing things they
shouldn't.

I've said it before but I'm going to say it again. There is *very clearly* a
theme in these cases, and *we found it using only math, with absolutely no
knowledge of the law.*


### Continuing Analysis of Communities

Just for fun, let's chart decisions by year and community for the six most
populated communities.

<figure>
<div id="chart-importance">
  select name, year, importance, community from decisions where community in (19, 192, 225, 249, 527, 635) order by importance desc limit 500;

  <script>
    dotChart(
      "#chart-importance",
      "/data/1612756205.csv",
      d => +d.year,
      d => +d.community,
      d => parseFloat(d.importance).toFixed(4),
      d => +d.community,
      d => truncateString(d.name, 80))
  </script>
</div>
<figcaption>Important cases by year and community. Larger dots are more
important. Community is on the Y axis.</figcaption>
</figure>

This gives us a sense of what sorts of things the law is focused on over time.
For example, since 2010 there's been a huge flurry of activity in community 249
(review of law.) Why? I don't know, but clearly something is going on. The
activity seems to be precipitated by *Dunsmuir v. New Brunswick,* so what we're
seeing is all the fallout from that case.

And we can see that community 192 (police being naughty) was very active from
1985 to 1995, but quieted down until a spike in 2009, and has been quiet since
2014. Maybe the police have been on good behavior since then?


## Conclusion

I've now been writing for eight hours straight, and I can no longer reliably
spell "jurisdiction." So it's time to finish this up and then go directly to
bed.

Personally, I find it fascinating just how much information can be gleamed from
nothing but citation data and some clever choices of visualizations. The biggest
takeaways in terms of policy from this project in my opinion are:

* The amount of case law is growing super-linearly --- and, horrifyingly, the
  curve appears to be exponential. Despite every court generating law at a
  constant rate, the growth rate of courts themselves is increasing. *This is
  clearly an untenable system.*
* Most decisions become irrelevant after only one year; the vast majority of hem
    are forgotten after ten.
* Somewhere between 33% and 50% of all decisions just follow precedent. That's a
    waste of everyone's time and the countries resources. There are huge
    efficiencies to be gained here if we can find a way of automating that
    stuff.

In aggregate, this means our legal system is doing a huge amount of work
churning out an ever growing number of decisions which get added to the annals
of time --- a good chunk of which are completely trivial, and almost all of
which are forgotten soon after. This is extremely good evidence that the court
system structuring itself as an [append-only
datastructure](https://en.wikipedia.org/wiki/Append-only) is a bad design.
There's no reason to continuously write down the answer you already know, and
never check it again; automate that stuff, don't add it to the corpus of law,
and save the courts for more important matters.

While we're talking about automating things, someone could *definitely* use the
community-finding algorithm to put the poor bastard responsible for adding
keywords to case summaries out of his misery.

Some intriguing takeaways, with no relevance to anything:

* There appear to be many extremely important decisions (in terms of influence)
    that are not well-enough recognized to be on Wikipedia. Is this a flaw in
    Wikipedia's coverage, or is the importance of these cases unknown to the
    world of law?
* This math stuff is actually useful for real-life things.

If you're interested in running your own analysis on this data without needing
to scrape CanLII for a few weeks, [it's available as a sqlite3
database.](https://mega.nz/file/YBomET6L#M2oBRiIRQTN_YJ4eiFiDjlkdNrEf8jbQG2a0wLkahNs)
Hidden in the HTML of this page are all of the queries I ran to produce the
graphs. Feel free to get in touch if you find anything interesting, I'd be happy
to update this page with, or linking to, your discoveries.

