---
layout: post
title: Encasing Taylor Swift
date: 2015-08-13 11:29
comments: true
tags: math, fun
---

I'm not much of a reddit guy, but I just found a neat one:
[r/theydidthemath][math]. Here's the gist: people ask silly questions, and other
people looking to do some mathematical recreation answer their silly questions.

[math]: https://www.reddit.com/r/theydidthemath/

[Here's one][taylor] that tickled my fancy:

[taylor]: https://www.reddit.com/r/theydidthemath/comments/3gsos3/request_if_you_took_the_net_worth_of_taylor_swift/

> If you took the net worth of Taylor Swift, in &#36;20 bills, and used those as
> building blocks, how big of an enclosure could you build around her and still
> have it remain soundproof?

Great question. Let's see if we can figure it out.

A [quick google search][netwo] indicates that Taylor Swift's net worth is
&#36;240 million USD. WolframAlpha, the source of all sorts of fantastic and
weird mathematical facts, [states][bill] the volume of a &#36;20 USD bill is
$1138 \text{mm}^3$, which gives us an easy $2.4\cdot 10^8 \text{USD} \div 20
\times 1138 \text{mm}^3\text{/ USD} = 136.5 \text{m}^3$ of building material to
work with[^1].

[^1]: The original version of this post accidentally calculated this in terms of
&#36;1 USD bills, so this number was off by a factor of $20$. Thanks to James
Barton for spotting this error.

[netwo]: https://www.google.com/search?q=net%20worth%20of%20taylor%20swift
[bill]: http://www.wolframalpha.com/input/?i=volume+of+a+%2420+USD+bill

Good start.

We will assume an enclosure around Taylor Swift is a hemisphere shell, and for
good measure, we'll pad the floor of the enclosure as well. The volume of a
hemisphere is

$$
v = \frac{4 \pi \left(r_o^3 - r_i^3\right)}{6}
$$

where $r_o$ and $r_i$ are the outer and inner radii of the sphere, respectively.
Since sound attenuates over distance, it would be more helpful to describe $r_i$
as the attenuation distance (which is to say, the necessary thickness of our
shell). We rewrite the hemisphere's volume as:

$$
v = \frac{4 \pi \left(r^3 - (r-s)^3\right)}{6}
$$

where $s$ is now the shell thickness, and $r$ is the outer radius.

We now need to add the floor of the enclosure, and since hemispherical shells
with a floor aren't very popular, we'll need to do the mathematics ourselves. We
can model the floor as a bunch of infinitesimally thin of cylinders of varying
radii:[^2]

[^2]: The original version of this post approximated this floor as a single
cylinder, which is a good approximation only for small $s$. Thanks to Marius van
Voorden for spotting this error.

Let $l$ be the total height of the stacked cylinders, and thus volume of our
floor's enclosure is:

$$
\int_0^s \pi \left((r-s) \sqrt{1 - \left(\frac{l}{r-s}\right)^2}\right)^2 dl =
\frac{1}{3} \pi s \left(3r^2 - 6rs + 2s^2\right)
$$

Add this to our hemisphere, and the total volume of our enclosure, after
simplifying, is thus:

$$
v = \frac{1}{3} \pi s \left(2s - 3r\right)^2
$$

Onwards. I don't know much about sound attenuation, but according to [this
page][atten], sound dissipates according to the law:

[atten]: https://www.nde-ed.org/EducationResources/CommunityCollege/Ultrasonics/Physics/attenuation.htm

$$
A = A_0 e^{-\alpha x}
$$

where $A_0$ is the initial loudness, $A$ is the resulting loudness,  $\alpha$ is
the attenuation coefficient of the material, and $x$ is the distance the
sound travels through the material.

The initial question doesn't state if we're trying to sound-proof Taylor Swift
or *a Taylor Swift concert*, so let's try doing both. We assume Taylor will be
shouting, so [we'll aim to sound-proof her up to][loudn2] $A_0 = 78 \text{dB}$ A
rock (we're being generous, here) [concert is approximately][loudn] $A_0 = 115
\text{dB}$. We assume dampening the sound down to the loudness of a whisper is
acceptable, so this gives us $A = 30 \text{dB}$.

[loudn]: http://www.gcaudio.com/resources/howtos/loudness.html
[loudn2]: http://www.engineeringtoolbox.com/voice-level-d_938.html

Solving our attenuation for $x$ (which is $s$, the necessary width of our shell
to achieve sound dampening), we get:

$$
s = \frac{\ln{A_0}-\ln{A}}{\alpha}
$$

Great! So given $\alpha$, we should be able to compute $s$. Strangely, there
doesn't seem to be much in the literature for the sound attenuation coefficient
for paper, so we'll have to use an educated guess here. [This page][coeff] gives
coefficients for a few common engineering materials, the closest to paper of
which is probably cork.

[coeff]: http://www.engineeringtoolbox.com/accoustic-sound-absorption-d_68.html

If you were going to *actually build* this enclosure around poor Taylor, you
would probably want to experimentally find a value for this (and have some
*really* good lawyers), but we'll assume
cork is close enough to paper to continue our analysis.

Substituting in $\alpha = 0.15$, the mean coefficient listed for cork, we get:

$$
s_t = \frac{\ln{78}-\ln{30}}{0.15} = 6.4 \text{m}  \\\\
s_c = \frac{\ln{115}-\ln{30}}{0.15} = 9.0 \text{m} \\\\
$$

where $s_t$ is the necessary shell width to silence Taylor Swift, and $s_c$, to
silence her concert.

Because doing math is hard, we'll use WolframAlpha [to do the remaining
calculations for us][answer]:

[answer]: http://www.wolframalpha.com/input/?i=solve+%28136.5+%3D+1%2F3+pi+s+%282+s-3+r%29%5E2+with+s+%3D+6.4%29+for+r

...which gives us radii smaller than the necessary shell width for the speaking
case. Since this is physically impossible, we conclude that such an enclosure
can't actually be constructed. Shame.

**But wait!** We totally fudged that $\alpha = 0.15$ number for cork. But maybe
paper attenuates more like snow? Maybe not, but hey, we've got nothing to work
with otherwise. We recompute $s_t$, $s_c$:

$$
s_t = \frac{\ln{78}-\ln{30}}{0.75} = 1.3 \text{m}  \\\\
s_c = \frac{\ln{115}-\ln{30}}{0.75} = 1.8 \text{m} \\\\
$$

and again run them through WolframAlpha. This time things look better, we get:

$$
r_t = 4.2 \text{m} \\\\
r_c = 4.0 \text{m}
$$

Success! If you want to silence just Taylor Swift, your enclosure can be $4.2
\text{m}$ in radius, and to silence her concert, you lose less than a meter in
total radius. Which is super cool, and actually pretty surprising. So, if paper
attenuates like snow, you *can* enclose Taylor Swift in her own money and have
her play a concert that no one will ever hear.

Marvelous.

