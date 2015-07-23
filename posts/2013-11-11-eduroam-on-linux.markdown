---
layout: post
title: A Working Eduroam Connection!
date: 2013-11-11 17:24
comments: true
tags: technical
---

My life over the last few months has been a living hell, and it's almost
entirely been [eduroam]'s fault. For those of you who don't know what eduroam
is:

* it's a wireless network supported at most universities
* this blog post is not for you.

[eduroam]: https://www.eduroam.org/

For those of you who DO know what eduroam is, however, you've probably noticed
that it doesn't work well (if at all) on Linux. Why? Nobody seems to know, but
today I got fed up with not having wireless on campus and decided to see if I
could figure it out.

The good news: I was successful. The bad news is that my solution is pretty
roundabout, and I'm not entirely sure what's necessary. Irregardless, I've
decided to share it with you, just in case somebody is running into the same
issues and are otherwise being failed by their google-fu.

I can only claim this will work on Debian, and even then, there are no
guarantees, and I am not liable if something breaks.

So, first things first, I got rid of any built-in network managers, deciding to
roll with my boy on the command line, *wpa_supplicant* (and *wpagui* if I ever
really need a connection manager).

    $ sudo apt-get install openssl wget wpasupplicant wpagui

Next, calculate the hash of your password so you don't need to keep it in
plaintext:

    $ echo -n your-password-goes-here | iconv -t utf16le | openssl md4

With this, we're now ready to set up **/etc/wpa_supplicant.conf**:

    ctrl_interface=DIR=/run/wpa_supplicant GROUP=users
    eapol_version=1
    ap_scan=1
    fast_reauth=1
    update_config=1

    network={
          ssid="eduroam"
          key_mgmt=WPA-EAP
          eap=PEAP
          ca_cert="/usr/share/ca-certificates/mozilla/Eduroam.crt"
          phase2="auth=MSCHAPV2"
          identity="username@university.tld"
          password=hash:<hash from previous step>
    }

Make sure to fill in your identity, and put in the hash you just calculated.

Get the eduroam certificate:

    $ sudo mkdir -p /usr/share/ca-certificates/mozilla
    $ sudo wget -O /usr/share/ca-certificates/mozilla/Eduroam.crt https://www.eduroam.us/webfm_send/223

And prevent the default networking service, which thrashes with our new setup:

    $ sudo update-rc.d networking remove

Now, if you're lucky (which I wasn't), you should be now able to connect to (and
successfully use) eduroam:

    $ sudo wpa_supplicant -Dnl80211,wext -iwlan0 -c/etc/wpa_supplicant.conf &
    $ sudo dhclient wlan0

If you're unlucky, it will connect, and you'll get great speeds for a few
seconds, and then experience ridiculous amounts of packet loss. In my case, this
was caused by some tricky driver issues.

Check the output of:

    $ lsmod | grep iwlwifi

Should you get any output whatsoever, you're using the Intel iwlwifi drivers,
and you will probably experience the networking thrashing. The issue in
particular is that the wireless-n support is really spotty, and takes precedence
over the working interfaces.

Put the following into **/etc/modprobe.d/iwlwifi.conf**:

    options iwlwifi auto_agg=0 wd_disable=1 11n_disable=1 swcrypto=1

And then reload the iwlwifi module:

    $ sudo rmmod iwldvm iwlwifi
    $ sudo modprobe iwlwifi

Connect again. It'll probably work!

    $ sudo wpa_supplicant -Dnl80211,wext -iwlan0 -c/etc/wpa_supplicant.conf &
    $ sudo dhclient wlan0

Yay! Great success! Well done, everybody. Give yourself a pat on the back, and
enjoy that sweet, sweet eduroam access.

For those of you who are interested in an automated solution, you can try my new
[scython] script: [eduroam installer].

[scython]: https://github.com/Paamayim/scython
[eduroam installer]: https://github.com/Paamayim/scython/blob/master/scripts/eduroam.scy

---

Written on an eduroam connection.

