---
layout: post
title: "Canadian Case Law: Visualized"
date: 2021-02-08 09:00
comments: true
tags:
---

<script src="https://unpkg.com/d3-sankey@0.12.3/dist/d3-sankey.min.js"></script>
<script src="https://d3js.org/d3.v6.min.js"></script>
<script src="/js/charts.js"></script>
<link rel="stylesheet" href="/css/law.css">


## Overview

## Methodology

My assumption is that the citation graph of Canadian case law is sufficient to
find interesting data in the law. Unfortunately, this data doesn't seem to exist
in any convenient format. [CanLII](TODO) makes the data available on the web,
but doesn't provide any sort of downloadable database. So I needed to make my
own.

I wired up a small web-scraper that would connect to CanLII and crawl through
the hundreds of thousands of cases available there. My program would randomly
pick a case that had been mentioned in the citations another decision, but which
it hadn't yet explored. It would then go to that page, record all the cases it
cited, and then randomly pick a new page.

TODO: graph discovery gif

At first I prioritized the Supreme Court decisions --- assuming these were the
most important cases --- and then loaded the cases from each province's Court of
Appeal. After a few days, I'd discovered 323,596 cases from 217 different
courts, and explored 240,964 of them. In total, there were 1,332,193 citations
in the dataset. Frighteningly, this is nowhere near all of the case law (I'd
estimate it's maybe one tenth of the publicly-available cases), but if I waited
to collect all of it I'd never get any work done.

Despite the large number of cases, it's important to discuss just how little
data I've got *per* case. The totality of my data about cases is of this form:

<figure>
<table>
<TR><TH>name</TH>
<TH>year</TH>
<TH>lang</TH>
<TH>jurisdiction</TH>
<TH>court</TH>
<TH>fetched</TH>
</TR>
<TR><TD>Bamba c. R.</TD>
<TD>2019</TD>
<TD>fr</TD>
<TD>qc</TD>
<TD>qcca</TD>
<TD>1</TD>
</TR>
<TR><TD>R. v. Leach</TD>
<TD>2019</TD>
<TD>en</TD>
<TD>bc</TD>
<TD>bcca</TD>
<TD>1</TD>
</TR>
<TR><TD>R. v. Pruski</TD>
<TD>2006</TD>
<TD>en</TD>
<TD>on</TD>
<TD>oncj</TD>
<TD>0</TD>
</TR>
<TR><TD>Regina v. Imperial Optical Co. Ltd.</TD>
<TD>1972</TD>
<TD>en</TD>
<TD>on</TD>
<TD>oncj</TD>
<TD>1</TD>
</TR>
<TR><TD>Windheim c. Windheim</TD>
<TD>2012</TD>
<TD>en</TD>
<TD>qc</TD>
<TD>qcca</TD>
<TD>1</TD>
</TR>
</table>
<figcaption>decision data</figcaption>
</figure>

While all I know about citations is who cited whom:

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

You'll notice there's really nothing here. Just some case names, what year they
happened, what court they appeared in, and the cases they cite. That's it.
There's no court transcripts, list of presiding judges, content keywords, or
even information about who won. In principle I could have extracted the involved
parties by trying to tear apart the name, but it didn't seem like it would buy
me much.

To reiterate, there's nothing at all that we can use to learn what any
particular case was *about.* In this database, the vast majority of the
information available to us is which cases cite whom.


### Possible Issues

The Canadian legal system has existed much longer than the idea that information
should be freely available. While CanLII is an excellent source of data, it
explicitly states how complete its records are from each court. For example,
while CanLII has the entire corpus of Supreme Court decisions, it's only
maintained continuous coverage of the BC Court of Appeal (BCCA) since 1990. Other
courts have different starting dates for their continuous coverage.

This presents a systematic bias in our data, namely that more recent cases are
more readily available. To illustrate, the database contains 6,212 cases from the
BCCA before 1990, but 19,366 cases since. While we might be interested in
whether the volume of law is increasing over time, we must be careful to
restrict ourselves to the range of continuous coverage.

In case you're wondering --- no, it looks like the volume of law in BCCA has
been slowly decreasing since 1990:

<figure>
<div id="bcca-volume">
  select year, count(*) as count from decisions where court = 'bcca' and year >= 1990 and 2021 > year group by year;

  <script>
    lineChart(
      "#bcca-volume",
      "/data/1612394754.csv",
      "Year",
      d => +parseInt(d.year),
      "Number of Cases",
      d => +parseInt(d.count))
  </script>
</div>
<figcaption>number of cases in bcca since 1990</figcaption>
</figure>

Looking only at citation data introduces another systematic bias in the dataset:
older cases have had a longer time to accumulate citations. Because we mainly
keep track of relationships between cases, it's possible for recent cases to
contradict previous decisions. Such a case is clearly very important to the law,
but will fly under our radar until it becomes commonly cited.


## Determining Important Cases

The sheer size of the case law corpus is staggering. My dataset contains roughly
350,000 decisions --- a small fraction of the *actual law.* And this is a few
orders of magnitude larger than any human could possibly remember.

Thankfully, most of this data is noise. Most cases taken to court are decided
uninterestingly: the presiding judge simply defers to precedent and everyone
goes on their way. It's safe to say that decisions of this sort are unimportant.
In my opinion, the desired end-state of the law is for all cases to be decided
like this --- at that point, we've got a stable, entirely-predictable system.

But that is not (yet!) the world we live in. Some cases *are* interesting ---
for example, the ones which *set* precedent, and the ones which *contradict*
precedent. How can we find these cases?

> TODO: Can't do it like lawyers do

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

At time of writing, of the top 50 cases, 42 have Wikipedia articles. And among
those, 31 are described in the first sentence as either a "landmark" or a
"leading" case. That's a pretty good sign.

Without further ado, here are the 50 most important cases by my analysis:

<ol>
<li><a href="https://en.wikipedia.org/wiki/Dunsmuir_v_New_Brunswick">Dunsmuir v. New Brunswick</a></li>
<li><a href="https://en.wikipedia.org/wiki/Hunter_v_Southam_Inc">Hunter et al. v. Southam Inc.</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Oakes">R. v. Oakes</a></li>
<li>Housen v. Nikolaisen</li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Collins_(1987)">R. v. Collins</a></li>
<li><a href="https://en.wikipedia.org/wiki/Baker_v_Canada_(Minister_of_Citizenship_and_Immigration)">Baker v. Canada (Minister of Citizenship and Immigration)</a></li>
<li><a href="https://.en.wikipedia.org/wiki/R_v_Big_M_Drug_Mart_Ltd">R. v. Big M Drug Mart Ltd.</a></li>
<li><a href="https://en.wikipedia.org/wiki/Canada_(Minister_of_Citizenship_and_Immigration)_v_Khosa">Canada (Citizenship and Immigration) v. Khosa</a></li>
<li><a href="https://en.wikipedia.org/wiki/Reference_Re_BC_Motor_Vehicle_Act">Re B.C. Motor Vehicle Act</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Grant">R. v. Grant</a></li>
<li><a href="https://en.wikipedia.org/wiki/Re_Rizzo_%26_Rizzo_Shoes_Ltd">Rizzo &amp; Rizzo Shoes Ltd. (Re)</a></li>
<li><a href="https://en.wikipedia.org/wiki/Irwin_Toy_Ltd_v_Quebec_(AG)">Irwin Toy Ltd. v. Quebec (Attorney General)</a></li>
<li><a href="https://en.wikipedia.org/wiki/Andrews_v_Law_Society_of_British_Columbia">Andrews v. Law Society of British Columbia</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Edwards_Books_and_Art_Ltd">R. v. Edwards Books and Art Ltd.</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Stillman">R. v. Stillman</a></li>
<li><a href="https://en.wikipedia.org/wiki/Dr_Q_v_College_of_Physicians_and_Surgeons_of_British_Columbia">Dr. Q. v. College of Physicians and Surgeons of British Columbia</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_O%27Connor">R. v. O'Connor</a></li>
<li>R. v. M. (C.A.)</li>
<li><a href="https://en.wikipedia.org/wiki/RJR-MacDonald_Inc_v_Canada_(AG)">RJR-MacDonald Inc. v. Canada (Attorney General)</a></li>
<li>R. v. Lyons</li>
<li><a href="https://en.wikipedia.org/wiki/Pushpanathan_v_Canada_(Minister_of_Citizenship_and_Immigration)">Pushpanathan v. Canada (Minister of Citizenship and Immigration)</a></li>
<li>Newfoundland and Labrador Nurses' Union v. Newfoundland and Labrador (Treasury Board)</li>
<li>Alberta (Information and Privacy Commissioner) v. Alberta Teachers' Association</li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Morgentaler">R. v. Morgentaler</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Sharpe">R. v. Sharpe</a></li>
<li><a href="https://en.wikipedia.org/wiki/Canada_(Director_of_Investigation_and_Research)_v_Southam_Inc">Canada (Director of Investigation and Research) v. Southam Inc.</a></li>
<li><a href="https://en.wikipedia.org/wiki/Rodriguez_v_British_Columbia_(AG)">Rodriguez v. British Columbia (Attorney General)</a></li>
<li><a href="https://en.wikipedia.org/wiki/Blencoe_v_British_Columbia_(Human_Rights_Commission)">Blencoe v. British Columbia (Human Rights Commission)</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Keegstra">R. v. Keegstra</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Therens">R. v. Therens</a></li>
<li><a href="https://en.wikipedia.org/wiki/Thomson_Newspapers_Co_Ltd_v_Canada_(AG)">Thomson Newspapers Ltd. v. Canada (Director of Investigation and Research, Restrictive Trade Practices Commission)</a></li>
<li><a href="https://en.wikipedia.org/wiki/Law_Society_of_New_Brunswick_v_Ryan">Law Society of New Brunswick v. Ryan</a></li>
<li><a href="https://en.wikipedia.org/wiki/Schachter_v_Canada">Schachter v. Canada</a></li>
<li><a href="https://en.wikipedia.org/wiki/Law_v_Canada_(Minister_of_Employment_and_Immigration)">Law v. Canada (Minister of Employment and Immigration)</a></li>
<li>R. v. Garofoli</li>
<li>Bell ExpressVu Limited Partnership v. Rex</li>
<li><a href="https://en.wikipedia.org/wiki/Dagenais_v_Canadian_Broadcasting_Corp">Dagenais v. Canadian Broadcasting Corp.</a></li>
<li><a href="https://en.wikipedia.org/wiki/Eldridge_v_British_Columbia_(AG)">Eldridge v. British Columbia (Attorney General)</a></li>
<li><a href="https://en.wikipedia.org/wiki/Slaight_Communications_Inc_v_Davidson">Slaight Communications Inc. v. Davidson</a></li>
<li><a href="https://en.wikipedia.org/wiki/Prostitution_Reference">Reference re ss. 193 and 195.1(1)(C) of the criminal code (Man.)</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Seaboyer">R. v. Seaboyer;  R. v. Gayme</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Mills">R. v. Mills</a></li>
<li><a href="https://en.wikipedia.org/wiki/Suresh_v_Canada_(Minister_of_Citizenship_and_Immigration)">Suresh v. Canada (Minister of Citizenship and Immigration)</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Malmo-Levine;_R_v_Caine">R. v. Malmo-Levine; R. v. Caine</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Mann">R. v. Mann</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Buhay">R. v. Buhay</a></li>
<li><a href="https://en.wikipedia.org/wiki/R_v_Swain">R. v. Swain</a></li>
<li><a href="https://en.wikipedia.org/wiki/McKinney_v_University_of_Guelph">Mckinney v. University of Guelph</a></li>
<li>Toronto (City) v. C.U.P.E., Local 79</li>
<li><a href="https://en.wikipedia.org/wiki/Vriend_v_Alberta">Vriend v. Alberta</a></li>
</ol>

If you're a law professional, you might disagree with this list. Maybe the
ordering is wrong. Maybe there are some glaring omissions, or some strange
choices. Glaring omissions are probably caused by recency bias --- new important
decisions simply haven't had time to accumulate citations (and thus importance.)
The wrong ordering? That's just like, your opinion, man.

Of particular interest to me are the cases on this list that *aren't on
Wikipedia.* Assuming Wikipedia is a reasonable proxy for what lawyers think are
important cases, the missing articles here have previously-unacknowledged
importance.

Anyway. It seems like my calculated importance score correlates with real-world
importance. But let's try to falsify that hypothesis, and see if the
bottom-ranked cases have Wikipedia articles.

I checked. They don't. Not a single hit in the 50 I tried[^try-more]. I also
checked for Wikipedia articles on a randomly-selected set of 50 cases, in an
attempt to find the base-rate we should expect to see. Again, there wasn't a
single hit.

[^try-more]: I'd like to have checked a few thousand, but this is a very manual
  process.

These negative results add strong evidence that my importance score is
*measuring something real.*


### Statistical Biases

So we've successfully found important cases. You might be wondering "what courts
do all these important cases come from?" Good question:

<figure>
<div id="court-of-important-cases">
select court, count(*) as count from (select court from decisions order by importance desc limit 1000) x group by court having count > 20;
AND THEN ADD OTHER 1000 -

  <script>
    pieChart(
      "#court-of-important-cases",
      "/data/1612574997.csv",
      d => d.court,
      d => d.count)
  </script>
</div>
<figcaption>Courts of the top 1000 important cases</figcaption>
</figure>



<h3>Communities</h3>
top 5 decisions from top 5 communities:

<h4>administrative</h4>
sqlite> select name, year, url from decisions where community == 1144 order by importance desc limit 5;
Dunsmuir v. New Brunswick|2008|/en/ca/scc/doc/2008/2008scc9/2008scc9.html
Housen v. Nikolaisen|2002|/en/ca/scc/doc/2002/2002scc33/2002scc33.html
Baker v. Canada (Minister of Citizenship and Immigration)|1999|/en/ca/scc/doc/1999/1999canlii699/1999canlii699.html
Canada (Citizenship and Immigration) v. Khosa|2009|/en/ca/scc/doc/2009/2009scc12/2009scc12.html
Rizzo & Rizzo Shoes Ltd. (Re)|1998|/en/ca/scc/doc/1998/1998canlii837/1998canlii837.html


<h4>charter</h4>
sqlite> select name, year, url from decisions where community == 638 order by importance desc limit 5;
Hunter et al. v. Southam Inc.|1984
R. v. Collins|1987
R. v. Grant|2009
R. v. Stillman|1997
R. v. Therens|1985

<h4>also charter?</h4>
sqlite> select name, year, url from decisions where community == 226 order by importance desc limit 5;
R. v. Oakes|1986
R. v. Big M Drug Mart Ltd.|1985
Re B.C. Motor Vehicle Act|1985
Irwin Toy Ltd. v. Quebec (Attorney General)|1989
Andrews v. Law Society of British Columbia|1989

<h4>criminal/constitutional</h4>
sqlite> select name, year, url from decisions where community == 816 order by importance desc limit 5;
R. v. O'Connor|1995
R. v. Mills|1999
Mills v. The Queen|1986
R. v. Stinchcombe|1991
R. v. Regan|2002

<h4>criminal/constitutional</h4>
sqlite> select name, year, url from decisions where community == 666 order by importance desc limit 5;
R. v. M. (C.A.)|1996
R. v. Lyons|1987
R. v. Smith (Edward Dewey)|1987
R. v. Proulx|2000
R. v. Shropshire|1995







<figure>
<div id="chart1">
  select jurisdiction, count(*) as count from decisions group by jurisdiction having count > 10000;
  <script>
    pieChart(
      "#chart1",
      "/data/1612246436.csv",
      d => d.jurisdiction,
      d => d.count)
  </script>
</div>
<figcaption>number of decisions in the dataset by jurisdiction</figcaption>
</figure>

<figure>
<div id="chart2">
  select src_year, avg(count) as count from (select src_year, count(*) as count from expanded_citations where src_court = 'scc' group by src_hash) group by src_year order by src_year asc;
  <script>
    lineChart(
      "#chart2",
      "/data/1612295413.csv",
      "Year",
      d => +parseInt(d.src_year),
      "Avg Number of Citations",
      d => +parseFloat(d.count).toFixed(2))
  </script>
</div>
<figcaption>average number of citations from scc decisions by year</figcaption>
</figure>

<figure>
<div id="chart3">
  select src_year, avg(diff) as diff from (select src_year, src_year - dst_year as diff from expanded_citations where src_year >= dst_year and src_court = 'scc' group by src_hash) group by src_year order by src_year asc;
  <script>
    lineChart(
      "#chart3",
      "/data/1612294018.csv",
      "Year",
      d => +parseInt(d.src_year),
      "Avg Age of Citation",
      d => +parseFloat(d.diff).toFixed(2))
  </script>
</div>
<figcaption>average age of scc citation by year</figcaption>
</figure>

<figure>
<div id="chart4">
  select substr(url, 2, 2) as language, jurisdiction, court, count(*) as count from decisions where url not like '/fr/ca/%' group by language, jurisdiction, court having count > 1000;

  <script>
    sankey(
      "#chart4",
      "/data/1612331151.csv")
  </script>
</div>
<figcaption>overview of the data for courts with &gt; 1000 entries</figcaption>
</figure>

<figure>
<div id="chart6">
  select year, count(*) as count from decisions where court == 'scc' group by year;

  <script>
    lineChart(
      "#chart6",
      "/data/1612369480.csv",
      "Year",
      d => +parseInt(d.year),
      "Number of cases decided",
      d => +parseFloat(d.count).toFixed(2))
  </script>
</div>
<figcaption>number of scc decisions</figcaption>
</figure>

<figure>
<div id="chart5">
  select src_year, dst_jurisdiction, count(*) as count from expanded_citations where src_court = 'scc' group by src_year, dst_jurisdiction;

  <script>
    stackedArea(
      "#chart5",
      "/data/1612369600.csv",
      d => +d.src_year,
      d => d.dst_jurisdiction,
      d => +d.count)
  </script>
</div>
<figcaption>scc jurisdiction citation by year</figcaption>
</figure>


<figure>
<div id="chart-importance">
  select name, year, importance, community from decisions order by importance desc limit 100;

  <script>
    dotChart(
      "#chart-importance",
      "/data/1612462218.csv",
      d => +d.year,
      d => +d.community,
      d => parseFloat(d.importance).toFixed(4),
      d => +d.community,
      d => truncateString(d.name, 50))
  </script>
</div>
<figcaption>important cases by community</figcaption>
</figure>

<figure>
<div id="importance-over-time">
  select year, sum(importance) as count from decisions where court == 'scc' group by year;

  <script>
    lineChart(
      "#importance-over-time",
      "/data/1612474615.csv",
      "Year",
      d => +parseInt(d.year),
      "Number of cases decided",
      d => +parseFloat(d.count).toFixed(2))
  </script>
</div>
<figcaption>total importance score of scc decisions per year</figcaption>
</figure>

Uh oh. Maybe this is our recency bias at work??

<figure>
<div id="volume">
  select court, year, count(*) as count from decisions d where court in (select court from court_importance limit 10) and year >= (select year from coverage c where d.court = c.court) group by court, year;

  <script>
    multiLineChart(
      "#volume",
      "/data/1612507631.csv",
      d => d.court,
      d => +parseInt(d.year),
      d => +parseInt(d.count))
  </script>
</div>
<figcaption>volume of decisions by top courts, starting after date of continuing coverage</figcaption>
</figure>


<figure>
<div id="importance-by-court">
  select court, year, sum(importance) as sum from decisions d where court in (select court from court_importance order by sum desc limit 10) and year >= (select year from coverage c where d.court = c.court) and year >= 1970 and importance is not null group by court, year;




  <script>
    multiLineChart(
      "#importance-by-court",
      "/data/1612544918.csv",
      d => d.court,
      d => +parseInt(d.year),
      d => +parseFloat(d.sum).toFixed(4))
  </script>
</div>
<figcaption>volume of decisions by top courts, starting after date of continuing coverage</figcaption>
</figure>

<figure>
<div id="compare-important-communities">
  select year, sum(importance) as sum, community from decisions where community in (select community from decisions group by community order by sum(importance) desc limit 6) and year >= 1970 group by community, year;


  <script>
    multiLineChart(
      "#compare-important-communities",
      "/data/1612546082.csv",
      d => +d.community,
      d => +d.year,
      d => +parseFloat(d.sum).toFixed(4))
  </script>
</div>
<figcaption>important cases by community</figcaption>
</figure>

<figure>
<div id="compare-important-communities2">
  select year, avg(importance) as sum, community from decisions where community in (select community from decisions group by community order by sum(importance) desc limit 6) and year >= 1970 group by community, year;


  <script>
    multiLineChart(
      "#compare-important-communities2",
      "/data/1612546089.csv",
      d => +d.community,
      d => +d.year,
      d => +parseFloat(d.sum).toFixed(4))
  </script>
</div>
<figcaption>important cases by community</figcaption>
</figure>



<p><strong>Pellentesque habitant morbi tristique</strong> senectus et netus et malesuada fames ac turpis egestas. Vestibulum tortor quam, feugiat vitae, ultricies eget, tempor sit amet, ante. Donec eu libero sit amet quam egestas semper. <em>Aenean ultricies mi vitae est.</em> Mauris placerat eleifend leo. Quisque sit amet est et sapien ullamcorper pharetra. Vestibulum erat wisi, condimentum sed, <code>commodo vitae</code>, ornare sit amet, wisi. Aenean fermentum, elit eget tincidunt condimentum, eros ipsum rutrum orci, sagittis tempus lacus enim ac dui. <a href="#">Donec non enim</a> in turpis pulvinar facilisis. Ut felis.</p>

<h2>Header Level 2</h2>

<ol>
   <li>Lorem ipsum dolor sit amet, consectetuer adipiscing elit.</li>
   <li>Aliquam tincidunt mauris eu risus.</li>
</ol>

<blockquote><p>Lorem ipsum dolor sit amet, consectetur adipiscing elit. Vivamus magna. Cras in mi at felis aliquet congue. Ut a est eget ligula molestie gravida. Curabitur massa. Donec eleifend, libero at sagittis mollis, tellus est malesuada tellus, at luctus turpis elit sit amet quam. Vivamus pretium ornare est.</p></blockquote>

<p>Pellentesque habitant morbi tristique senectus et netus et malesuada fames ac turpis egestas. Vestibulum tortor quam, feugiat vitae, ultricies eget, tempor sit amet, ante. Donec eu libero sit amet quam egestas semper. Aenean ultricies mi vitae est. Mauris placerat eleifend leo. Quisque sit amet est et sapien ullamcorper pharetra. Vestibulum erat wisi, condimentum sed, commodo vitae, ornare sit amet, wisi. Aenean fermentum, elit eget tincidunt condimentum, eros ipsum rutrum orci, sagittis tempus lacus enim ac dui. Donec non enim in turpis pulvinar facilisis. Ut felis. Praesent dapibus, neque id cursus faucibus, tortor neque egestas augue, eu vulputate magna eros eu erat. Aliquam erat volutpat. Nam dui mi, tincidunt quis, accumsan porttitor, facilisis luctus, metus</p>

<p>Pellentesque habitant morbi tristique senectus et netus et malesuada fames ac turpis egestas. Vestibulum tortor quam, feugiat vitae, ultricies eget, tempor sit amet, ante. Donec eu libero sit amet quam egestas semper. Aenean ultricies mi vitae est. Mauris placerat eleifend leo. Quisque sit amet est et sapien ullamcorper pharetra. Vestibulum erat wisi, condimentum sed, commodo vitae, ornare sit amet, wisi. Aenean fermentum, elit eget tincidunt condimentum, eros ipsum rutrum orci, sagittis tempus lacus enim ac dui. Donec non enim in turpis pulvinar facilisis. Ut felis. Praesent dapibus, neque id cursus faucibus, tortor neque egestas augue, eu vulputate magna eros eu erat. Aliquam erat volutpat. Nam dui mi, tincidunt quis, accumsan porttitor, facilisis luctus, metus</p>

<h3>Header Level 3</h3>

<ul>
   <li>Lorem ipsum dolor sit amet, consectetuer adipiscing elit.</li>
   <li>Aliquam tincidunt mauris eu risus.</li>
</ul>

<pre><code>
#header h1 a {
  display: block;
  width: 300px;
  height: 80px;
}
</code></pre>

<p>Pellentesque habitant morbi tristique senectus et netus et malesuada fames ac turpis egestas. Vestibulum tortor quam, feugiat vitae, ultricies eget, tempor sit amet, ante. Donec eu libero sit amet quam egestas semper. Aenean ultricies mi vitae est. Mauris placerat eleifend leo. Quisque sit amet est et sapien ullamcorper pharetra. Vestibulum erat wisi, condimentum sed, commodo vitae, ornare sit amet, wisi. Aenean fermentum, elit eget tincidunt condimentum, eros ipsum rutrum orci, sagittis tempus lacus enim ac dui. Donec non enim in turpis pulvinar facilisis. Ut felis. Praesent dapibus, neque id cursus faucibus, tortor neque egestas augue, eu vulputate magna eros eu erat. Aliquam erat volutpat. Nam dui mi, tincidunt quis, accumsan porttitor, facilisis luctus, metus</p>

<p>Pellentesque habitant morbi tristique senectus et netus et malesuada fames ac turpis egestas. Vestibulum tortor quam, feugiat vitae, ultricies eget, tempor sit amet, ante. Donec eu libero sit amet quam egestas semper. Aenean ultricies mi vitae est. Mauris placerat eleifend leo. Quisque sit amet est et sapien ullamcorper pharetra. Vestibulum erat wisi, condimentum sed, commodo vitae, ornare sit amet, wisi. Aenean fermentum, elit eget tincidunt condimentum, eros ipsum rutrum orci, sagittis tempus lacus enim ac dui. Donec non enim in turpis pulvinar facilisis. Ut felis. Praesent dapibus, neque id cursus faucibus, tortor neque egestas augue, eu vulputate magna eros eu erat. Aliquam erat volutpat. Nam dui mi, tincidunt quis, accumsan porttitor, facilisis luctus, metus</p>


QUESTIONS TO ANSWER:

* is law getting more complicated?
  * more cases per year?
  * is the average age of citation going up?
  * average number of citations?
* what are the most important cases?
* can we discover what the communities mean?
  * do we see trends in these communities? wrt time, jurisdiction, language, importance
* how often do cases cite cases in other languages?
* are there "friendship clusters" in what courts cite? by jurisdiction?
* which courts hold the most power?
* did i accidentally completey misrepresent the french stuff? (NO)
* do num citations correlate with importance
  * importance with time?
* what percentage of cases are boring vs interesting?


