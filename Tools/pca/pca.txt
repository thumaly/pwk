#!/bin/sh
#! -*- perl -*-
eval 'exec perl -x -w $0 ${1+"$@"}'
  if 0;

# PCA - Patch Check Advanced
#       Analyze, download and install patches for Oracle Solaris
#
# Author : Martin Paul <martin.paul@univie.ac.at>
# Home   : http://www.par.univie.ac.at/solaris/pca/
my $version='20150327-01';

use strict;
use Config;

# Default paths
my $unzip= '/usr/bin/unzip';
my $showrev= '/usr/bin/showrev';
my $pkginfo= '/usr/bin/pkginfo';
my $pkgparam= '/usr/bin/pkgparam';
my $pkgchk= '/usr/sbin/pkgchk';
my $uncompress= '/usr/bin/uncompress';
my $tar= '/usr/sbin/tar';
my $uname= '/usr/bin/uname /bin/uname';
my $pager= '/usr/bin/more /bin/more';

# Supported options, format is:
#   Long name, short name, argument type, argument text, default value, help
my @options=(
  "list|l|||0|List patches",
  "listhtml|L|||0|List patches, produce HTML output",
  "download|d|||0|Download patches",
  "install|i|||0|Install patches",
  "pretend|I|||0|Pretend to install patches",
  "readme|r|||0|Display patch READMEs",
  "unzip|u|||0|Unzip patches",
  "getxref|x|||0|Download patch xref file",
  "xrefdir|X|s|DIR|/var/tmp|Location of patch xref file",
  "nocheckxref|y|||0|Do not check for updated patch xref file",
  "xrefown||||0|Give write permissions on xref file to user only",
  "nocache||||0|Tell proxy to not cache xref file",
  "patchdir|P|s|DIR|.|Patch download directory",
  "askauth|a|||0|DEPRECATED",
  "user||s|USER||My Oracle Support (MOS) user name",
  "passwd||s|PASS||My Oracle Support (MOS) password",
  "supplevel||||0|DEPRECATED",
  "patchurl||s|URL|oracle|Source for patches and READMEs (URLs or \"oracle\")",
  "xrefurl||s|URL|oracle|Source for patchdiag.xref (URLs or \"oracle\")",
  "stop||s@|ID||Stop after patch ID",
  "ignore||s@|WHAT||Ignore patches whose ID or synopsis match WHAT",
  "rec||s@|ID||Set Recommended flag on patch ID",
  "sec||s@|ID||Set Security flag on patch ID",
  "pattern|p|s|REGEX||List only patches whose synopsis matches REGEX",
  "noreboot|n|||0|Install only patches which do not require a reboot",
  "minage||i|DAYS|0|List only patches which are at least DAYS old",
  "maxage||i|DAYS|0|List only patches which are at most DAYS old",
  "nodep||||0|Do not resolve patch dependencies",
  "minimal||||0|Use minimal revision for recommended patches",
  "syslog||s|TYPE|daemon.notice|Log patch installs to syslog priority TYPE",
  "nobackup|k|s@|ID||Do not back up files to be patched for patch ID",
  "backdir|B|s|DIR||Saves patch backout data to DIR",
  "safe|s|||0|Check locally modified files for safe patch installation",
  "currentzone|G|||0|Make patchadd install patches in the current zone only",
  "patchadd||s|FILE|/usr/sbin/patchadd|Path to patchadd command",
  "noheader|H|||0|Don't display descriptive headers",
  "format||s|FORMAT|%p %i %e %c %r%s%b %a %y|Set output format to FORMAT",
  "fromfiles|f|s|DIR||Read uname/showrev/pkginfo output from files in DIR",
  "dltries||i|NUM|1|Try downloads from Oracle download server NUM times",
  "force|F|||0|Force local caching proxy to download from Oracle server",
  "root|R|s|DIR||Alternative root directory",
  "wget||s|FILE|/usr/sfw/bin/wget /usr/local/bin/wget /opt/csw/bin/wget /usr/bin/wget|Path to wget command",
  "wgetproxy||s|URL||Default proxy for wget",
  "wgetopt||s@|OPT||Feed option OPT directly to wget",
  "logger||s|FILE|/usr/bin/logger|Path to logger command",
  "threads|t|i|NUM|0|Use NUM download threads" . ($Config{useithreads} ? '' : ' (DISABLED, Perl lacks ithreads)'),
  "update||s|TYPE|never|Update pca (TYPE is never, check, now or auto)",
  "pcaurl||s|URL|http://www.par.univie.ac.at/solaris/pca/stable/|URL for pca update",
  "ssprot||s|PROT||DEPRECATED",
  "sshost||s|HOST||DEPRECATED",
  "ohost||s|HOST|getupdates.oracle.com|HOST name or IP address for Oracle patch server",
  "norootchk||||0|Skip check for root user with safe/install options",
  "cffile||s@|FILE||Read FILE as additional configuration file",
  "debug|V|||0|Print debug information",
  "help|h|||0|Display this help",
  "man|m|||0|Display manual page",
  "version|v|||0|Display version information",
  "operands||||missing|ENVFILE",
  "tmpdir||||/tmp|INTERNAL",
  "proxy||||0|INTERNAL",
  "pforce||||0|INTERNAL",
  "dbgfile||||/var/tmp/pca-proxy-debug.txt|INTERNAL"
);

# Modules
use Getopt::Long;
use Time::Local;
use Cwd;
use File::Path;
use Fcntl;
use File::Basename;
use File::Copy;

# Variable declarations
my (%o, %input, %p, %pkgs, %u, %c, %locks, %rloop, %x, %pkga);
my (@plist, @slist, @rlist);
my $conf_dbg=''; my %conf_read;
my $dlfile='';
my $sttyset=0;
my $patchxdir='';
my $currenttime=time();
my $queue;
my %a;
my $download_start;
my $stopreached=0;
my %wget=(path=>'', version=>0, proto=>'', error=>'', rc=>'');
my $agesum=0;
my $xval=0;
my %timing; $timing{start}=time();
my $htmladditionalout="";

# Force flush to stdout right after every print command without "\n"
$|= 1;

# Set signal handler
$SIG{HUP} = 'IGNORE';
$SIG{TERM} = $SIG{INT} = $SIG{QUIT} = \&handler;

# Main
#
parse_args();
check_prerequisites();
import_threads();
process_patch_exceptions();
process_patch_flags();
update();

$o{proxy} && proxy();
$o{supplevel} && supplevel();

expand_operands();

if ($o{readme} && !$o{list} && !$o{download} && !$o{install} && ("@slist" =~ /^(\d{6}-\d{2} *)+$/)) {
  foreach my $pp (@slist) {
    my ($id, $rev)= split (/-/, $pp); init_patch ($id); push (@plist, $pp);
  }
  do_patch_list();
  exit $xval;
}

get_current_xref();
if (!$o{list} && !$o{download} && !$o{install} && !$o{readme}) { exit $xval }

get_uname();
get_installed_packages();
get_installed_patches();
get_current_patches();
set_extra_req();
create_patch_list();
print_header();
do_patch_list();
print_footer();

exit $xval;

# Functions

sub download_patch_worker  {
  my $pp;
  {  # signal the download loop that we're ready...
    lock $download_start;
    if (!defined($download_start)) {  # if we haven't already
      $download_start = 0;
      dbg ("Broadcasting download worker ready");
      cond_broadcast(\$download_start);
    }
  }
  {  # wait for the download loop to tell us to start
    lock $download_start;
    dbg ("Waiting for download loop broadcast");
    cond_wait(\$download_start) until $download_start == 1;
  }
  while (defined($pp = $queue->dequeue())) {
    my ($id, $rev) = split /-/, $pp;
    BEGIN { $^W = 0 }
    $p{$id}{worker_tid} = threads->self->tid();
    BEGIN { $^W = 1 }
    $p{$id}{worker_done} = 0;
    dbg ("Worker " . $p{$id}{worker_tid} . " downloading " . $pp);
    download_patch($pp);
    $p{$id}{worker_done} = 1;
  }
  $queue->enqueue(undef);
}

sub buffer_worker_out {
  my $id = shift;
  my $cat = shift;

  if (!$o{threads}) {
    return (out ($cat, @_));
  }

  my $ar = &share([]);
  @{$ar} = ($cat, @_);
  lock $p{$id};
  push @{$p{$id}{output}}, $ar;
}

sub unbuffer_worker_out {
  my $id = $_[0];
  lock $p{$id};
  while (my $ar = shift @{$p{$id}{output}}) {
    if (@{$ar}) {
      my $cat = shift @{$ar};
      out ($cat, @{$ar});
    }
  }
}

sub do_patch_list {
  (@plist) || return;

  my @workers;
  for (my $i = 0; $i < $o{threads}; $i ++) {
    dbg ("Creating worker");
    BEGIN { $^W = 0 }
    push @workers, threads->new(\&download_patch_worker);
    BEGIN { $^W = 1 }
  }

  # Counters
  $c{current}=0;
  $c{total}=$#plist+1;
  $c{dl}=$c{skipdl}=$c{faildl}=$c{inst}=$c{skipinst}=$c{failinst}=0;
  $c{p_ci}=$c{p_bi}=$c{p_c}=$c{p_b}=0;

  my @pplist=();
  if ("@plist" =~ /^(\d{6}-\d{2} *)+$/) {
    @pplist=@plist;
  } else {
    foreach my $id (@plist) {
      # Add revision to patch id
      my $pp="";
      ($p{$id}{irev} ne "00") && ($pp="$id-$p{$id}{irev}");
      ($p{$id}{crev} ne "00") && ($pp="$id-$p{$id}{crev}");
      ($p{$id}{prev} ne "00") && ($pp="$id-$p{$id}{prev}");
      $pp || errx ("Unknown patch-id $id");
      push (@pplist, $pp);
    }
  }
  if ($o{threads}) {
    foreach my $pp (@pplist) { $queue->enqueue($pp) }
    $queue->enqueue(undef);
  }

  foreach my $pp (@pplist) {
    $c{current}++;
    my ($id, $rev)= split (/-/, $pp);

    if ($o{list} || $o{download} || $o{install}) {
      print_patch ($id);
    }
    if ($o{download} || $o{unzip} || $o{install}) {
      out ('info', "\nLooking for $pp ($c{current}/$c{total})");
      if ($o{threads}) {
        {  # wait for the first download worker to tell us it's ready...
          lock $download_start;
          if (!defined($download_start)) {  # if it hasn't already
            dbg ("Waiting for download worker broadcast");
            cond_wait(\$download_start) until (defined($download_start) && $download_start == 0);
          }
        }
        {  # signal download workers to start...
          lock $download_start;
          if(defined($download_start) && $download_start != 1) {  # if we haven't already
            $download_start=1;
            dbg ("Broadcasting download loop ready");
            cond_broadcast(\$download_start);
          }
        }
        while(!defined $p{$id}{worker_done} || !$p{$id}{worker_done}) {
          unbuffer_worker_out ($id);
          sleep 1;
        }
        unbuffer_worker_out ($id);
      }
      else {
        download_patch($pp);
      }
    }
    if ($o{unzip}) {
      out ('info', "\nUnzipping $pp ($c{current}/$c{total})");
      if (-d "$o{patchdir}/$pp") {
        out ('info', "Skipped - directory exists");
      } else {
        my @out = ();
        my $cmd = "$unzip -d $o{patchdir} -q $o{patchdir}/$pp.zip"; dbg ($cmd);
        open (CMD, "$cmd </dev/null 2>&1|");
        while (<CMD>) { chomp; dbg ($_); push (@out, $_) }
        close (CMD);
        if ($?) {
          out ('error', "Failed with exit code: $?");
          foreach my $i (@out) { out ('info', "$i") }
        } else {
          out ('info', "Done");
        }
      }
      if ($p{$id}{dfori}) { unlink ("$o{patchdir}/$pp.zip") }
    }
    if ($o{install}) {
      out ('info', "\nInstalling $pp ($c{current}/$c{total})");
      install_patch($pp);
      if (-x '/var/run/nopatch') {
        `/var/run/nopatch`;
        $xval=3;
        last
      }
    }
    if ($o{readme}) {
      my $rtmp=get_readme ($pp);
      ($rtmp) && (push (@rlist, $rtmp));
    }
    ($o{download} || $o{unzip} || $o{install}) && out ('info', '-' x 78);
  }

  foreach my $worker (@workers) {
    dbg ("Waiting for worker");
    $worker->join();
  }

  if ($o{download} || $o{install}) {
    printf "Download Summary: %d total, %d successful, ", $c{total}, $c{dl};
    printf "%d skipped, %d failed\n", $c{skipdl}, $c{faildl};
  }
  if ($o{install}) {
    printf "Install Summary : %d total, %d successful, ", $c{total}, $c{inst};
    printf "%d skipped, %d failed\n", $c{skipinst}, $c{failinst};

    if (!$o{root} || ($o{root} eq "-R /")) {
         if ($c{p_ci}) { out ('info', "\nReconfiguration reboot required (init 6)"); $xval || ($xval=4) }
      elsif ($c{p_bi}) { out ('info', "\nReboot required (init 6)"); $xval || ($xval=4) }
      elsif ($c{p_c }) { out ('info', "\nReconfiguration reboot recommended (init 6)"); $xval || ($xval=5) }
      elsif ($c{p_b }) { out ('info', "\nReboot recommended (init 6)"); $xval || ($xval=5) }
    }
  }
  if ($o{readme} && (@rlist)) {
    system ("$pager @rlist");
    unlink (@rlist);
  }
}

sub expand_operands {
  my @tlist=@ARGV; my $again=1; my %fc;

  while ($again) {
    $again=0; @slist=();
    foreach my $s (@tlist) {
      if ($s =~ /^(missingr?s?|installedr?s?|allr?s?|totalr?s?|unbundledr?s?|badr?s?)$/) {
        push (@slist, $s);
      } elsif ($s =~ /^(mr?s?|ir?s?|ar?s?|tr?s?|ur?s?|br?s?)$/) {
        push (@slist, $s);
      } elsif ($s =~ /^(\d{6}|\d{6}-\d{2})$/) {
        push (@slist, $s);
      } elsif ($s =~ /(\d{6}-\d{2})\.(zip|jar|tar\.Z|tar)$/) {
        push (@slist, $1);
      } elsif (-f $s) {
        if ($fc{$s}) { errx ("Recursive file inclusion: $s") } else { $fc{$s}=1 }
        open (LIST, "<$s") || errx ("Can't open $s ($!)");
        while (<LIST>) {
          chomp;
          next unless $_;
          push (@slist, (split (/ /, $_))[0]);
          $again=1;
        }
      } else {
        errx ("Unknown operand: $s");
      }
    }
    @tlist=@slist;
  }
  dbg ("Expanded patch list: @slist");
  if ($o{minimal} && ("@slist" !~ /^mr$|^missingr$/)) {
    print ("WARNING: Using --minimal with a patch group other than missingr!\n");
  }
}

sub create_patch_list {
  if ("@slist" =~ /^(\d{6}-\d{2} *)+$/) {
    dbg ("All operands are fully qualified patch IDs plus revisions");
    foreach my $pp (@slist) {
      my ($id, $rev)= split (/-/, $pp); init_patch ($id); push (@plist, $pp);
    }
    return;
  }

  # Put patches for patch utilities at the top of the list
  my @putil=();
  foreach my $id (sort keys %p) {
    if ($p{$id}{pkgs} =~ /SUNWswmt:/) { push (@putil, $id) }
  }
  dbg ("SUNWswmt patches: @putil");

  foreach my $id (@putil, sort keys %p) {
    add_patch_list ($id,0);
  }
}

sub add_patch_list {
  my $id=$_[0];
  my $type=$_[1];

  # Ignore patches which have been listed already.
  ($p{$id}{listed}) && return (0);

  $type=match_patch_list($id,$type);
  $type || return (0);

  if ($id eq "125547") {
    $p{$id}{requires}="122660-10";
    $p{"122660"}{obs}=0; $p{"122660"}{obsoletedby}="";
    $p{"124204"}{obs}=0; $p{"124204"}{obsoletedby}="";
    $p{"118731"}{obs}=0; $p{"118731"}{obsoletedby}="";
  }
  if ($id eq "125548") {
    $p{$id}{requires}="122661-08";
    $p{"122661"}{obs}=0; $p{"122661"}{obsoletedby}="";
    $p{"124205"}{obs}=0; $p{"124205"}{obsoletedby}="";
  }

  if (($p{$id}{requires} ne '') && !$o{nodep}) {
    REQ: foreach my $r (split (/;/, $p{$id}{requires})) {
      # Fix required patches which were never released
      ($r eq "125077-02") && ($r="120011-09"); # 119757
      ($r eq "125078-02") && ($r="120012-10"); # 119758
      ($r eq "125486-01") && ($r="120011-14"); # 126206
      ($r eq "125487-01") && ($r="120012-14"); # 126207
      ($r eq "126677-02") && ($r="124628-03"); # 119534, 124630
      ($r eq "126678-02") && ($r="124629-03"); # 119535, 124631
      ($r eq "114431-03") && ($r="117172-17"); # 116473

      my ($r_id, $r_rev)= split (/-/, $r);

      # If a required patch has been obsoleted by another patch, we
      # continue with the patch that obsoleted it.
      while ($p{$r_id}{obsoletedby} ne '') {
        my ($oby_id, $oby_rev)= split (/-/, $p{$r_id}{obsoletedby});
        dbg ("$r_id-$r_rev required by $id: obsolete, replaced with $oby_id-$oby_rev");
        ($r_id, $r_rev)= ($oby_id, $oby_rev);
      }
      # Check if patch requires itself
      if ($r_id eq $id) {
        dbg ("$r_id-$r_rev required by $id: patch requires itself");
        next;
      }
      # Check if the required patch is in our database. Normally we should
      # stop with an error here, but maybe information in patchdiag.xref
      # is wrong and the patch will install without the missing required patch.
      if ($p{$r_id}{crev} eq "00") {
         dbg ("$r_id-$r_rev required by $id: unknown patch");
         next;
      }
      # Ignore patches already in our list.
      if ($p{$r_id}{listed}) {
        dbg ("$r_id-$r_rev required by $id: already listed");
        next;
      }
      # Ignore patches already installed.
      if ($p{$r_id}{irev} ge $r_rev) {
        dbg ("$r_id-$r_rev required by $id: already installed");
        next;
      }
      # Ignore patches which are ignored
      if (!check_ignore($r_id, $r_rev)) {
        dbg ("$r_id-$r_rev required by $id: set to ignore");
        next;
      }
      # Check for circular patch dependencies.
      if ($p{$r_id}{requires} ne '') {
        foreach my $s (split (/;/, $p{$r_id}{requires})) {
          (my $s_id, my $s_rev)= split (/-/, $s);
          if (exists $rloop{"$r_id:$s_id"}) {
            dbg ("$r_id-$r_rev required by $id: Circular patch dependency");
            next REQ;
          }
          $rloop{"$r_id:$s_id"} = 1;
        }
      }

      dbg ("$r_id-$r_rev required by $id");
      if (!add_patch_list($r_id,$type)) {
        dbg ("$r_id-$r_rev required by $id: does not match");
      }
    }
  }
  $p{$id}{listed}=1;
  push (@plist, $id); $agesum+=calculateage($id);
  return (1);
}

sub match_patch_list {
  my $id=$_[0];
  my $type=$_[1];
  my $found;

  S: foreach my $s (@slist) {
    # Complete patch id with revision (123456-78)
    if ($s =~ /\d{6}-\d{2}/) {
      my ($s_id,$s_rev)= split(/-/,$s);
      if ($id eq $s_id) {
        if (!check_ignore($id, $s_id)) { next }
        $p{$id}{prev}=$s_rev;
        return (1);
      }
    }
    # Incomplete patch id (123456)
    if ($s =~ /\d{6}/) {
      if (($id eq $s) || ($type == 2)) {
        if (!check_ignore($id, $p{$id}{crev})) { next }
        return (2);
      }
    }
    # installed or all
    if (($s =~ /^i/) || ($s =~ /^a/)) {
      if (!check_ignore($id, $p{$id}{crev})) { next }
      if (!check_rs($s,$id)) { next }

      # Check if patch is installed.
      if ($p{$id}{irev} ne '00') { return (3); }
    }
    # unbundled
    if ($s =~ /^u/) {
      # Check if patch is Unbundled and has an empty packages list.
      if (!(($p{$id}{os} eq "Unbundled") && ($p{$id}{pkgs} eq ""))) { next }

      # Ignore obsolete and bad patches
      if ($p{$id}{obs} || $p{$id}{bad}) { next }

      if (!check_ignore($id, $p{$id}{crev})) { next }
      if (!check_rs($s,$id)) { next }

      return (4);
    }
    # missing or all
    if (($s =~ /^m/) || ($s =~ /^a/)) {
      # Ignore obsolete and bad patches
      if ($p{$id}{obs} || $p{$id}{bad}) { next }

      # Ignore patches which are installed in the current or higher revision
      if ($p{$id}{irev} ge $p{$id}{crev}) { next }

      # Ignore patches for packages that are not installed or that don't
      # match the installed package's version and architecture
      $found=0;
      PKG: foreach my $j (split (/\;/, $p{$id}{pkgs})) {
        my ($package, $version)= split (/:/, $j, 2);
        next unless ($pkgs{$package});
        my $iversion=$pkgs{$package};
        if ($iversion =~ /<\Q$version\E>/) {
          foreach my $a (split (/\;/, $p{$id}{archs})) {
            if ($pkga{$package} =~ /<\Q$a\E>/) { $found=1; last PKG }
          }
        }
      }
      if (!$found) { next }

      # Ignore patches that don't meet the extra requirements
      if (!chk_extra_req($id)) { next }

      if (!check_ignore($id, $p{$id}{crev})) { next }
      if (!check_rs($s,$id) && ($type != 5)) { next }

      return (5);
    }
    # Total set of patches
    if ($s =~ /^t/) {
      if ($p{$id}{crev} eq "00") { next }
      if (!check_ignore($id, $p{$id}{crev})) { next }
      if (!check_rs($s,$id)) { next }

      return (6);
    }
    # Installed bad patches
    if ($s =~ /^b/) {
      if (!$p{$id}{ibad}) { next }

      # Check if bad patch has been obsoleted by an installed patch
      my $oby_id= $id; my $oby_rev;
      while ($p{$oby_id}{obsoletedby} ne '') {
        ($oby_id, $oby_rev)= split (/-/, $p{$oby_id}{obsoletedby});
        if ($p{$oby_id}{irev} ge $oby_rev) { next S; }
      }
      if (!check_ignore($id, $p{$id}{crev})) { next }
      if (!check_rs($s,$id)) { next }

      return (7);
    }
  }
  return (0);
}

sub check_ignore {
  my $id=$_[0]; my $rev=$_[1];

  # Ignore patches in the ignore list.
  if ($p{$id}{ignore} eq "00") { return (0) }
  if ($p{$id}{ignore} ge $rev) { return (0) }
  foreach my $i (@{$o{ignore}}) {
    next if ($i =~ /^\d{6}$|^\d{6}-\d{2}$/);
    if ($p{$id}{synopsis} =~ /$i/) { return (0) }
  }
  return (1);
}

sub check_rs {
  my $s=$_[0]; my $id=$_[1];

  # Check that a "stop" patch hasn't been seen
  if ($stopreached) { return(0) }

  # Check that this isn't a "stop" patch
  if ($p{$id}{stop} eq "00") { $stopreached = 1; }
  if ($p{$id}{stop} eq $p{$id}{crev}) { $stopreached = 1; }

  # Check for R/S flags
  if ($s =~ /rs$/) {
    if (!($p{$id}{rec} || $p{$id}{recf} || $p{$id}{sec} || $p{$id}{secf})) { return(0) }
  } else {
    if (($s =~ /r$/) && (!$p{$id}{rec}) && (!$p{$id}{recf})) { return(0) }
    if (($s =~ /s$/) && (!$p{$id}{sec}) && (!$p{$id}{secf})) { return(0) }
  }

  # Check for minage, maxage and pattern
  if (($o{minage}) && (calculateage($id) < $o{minage})) { return(0) }
  if (($o{maxage}) && (calculateage($id) > $o{maxage})) { return(0) }
  if ($o{pattern}) {
    if ($o{pattern} =~ /^!/) {
      my $pattern= substr ($o{pattern}, 1);
      if ($p{$id}{synopsis} =~ /$pattern/) { return (0) }
    } else {
      if ($p{$id}{synopsis} !~ /$o{pattern}/) { return(0) }
    }
  }

  return(1);
}

sub download_patch {
  my $pp=$_[0];
  my ($id, $rev)= split (/-/, $pp);

  lock_free($o{patchdir}, "download.$pp", 300) || errx ("Another instance of pca is downloading $pp to $o{patchdir} right now");

  # Check if patch exists
  if (-d "$o{patchdir}/$pp") {
    buffer_worker_out ($id, 'info', "Found patch directory"); $c{skipdl}++; return;
  }
  foreach my $ext ('zip','jar','tar.Z','tar') {
    (-z "$o{patchdir}/$pp.$ext") && unlink "$o{patchdir}/$pp.$ext";
    if (-f "$o{patchdir}/$pp.$ext") {
      buffer_worker_out ($id, 'info', "Found patch file"); $c{skipdl}++; return;
    }
  }

  # Remember if we downloaded the patch for unzip/install only
  $o{download} || ($p{$id}{dfori}=1);

  (-w $o{patchdir}) || errx ("Can't write to patch download directory $o{patchdir}");

  lock_create($o{patchdir}, "download.$pp", 1) || errx ("Another instance of pca is downloading $pp to $o{patchdir} right now");

  PATCHURL: foreach my $patchurl (split (/\s/, $o{patchurl})) {
    if ($patchurl =~ /^file:\/|^\//) {
      buffer_worker_out ($id, 'info', "Trying $patchurl");
      my $path=$patchurl; $path =~ s/^file://;
      foreach my $ext ('zip','jar','tar.Z','tar') {
        if (-r "$path/$pp.$ext") {
          my ($atime, $mtime) = (stat("$path/$pp.$ext"))[8,9];
          copy ("$path/$pp.$ext", "$o{patchdir}/$pp.$ext");
          utime $atime, $mtime, "$o{patchdir}/$pp.$ext";
        }
        if (-s "$o{patchdir}/$pp.$ext") {
          buffer_worker_out ($id, 'info', "Done"); $c{dl}++; goto DONE;
        }
        unlink "$o{patchdir}/$pp.$ext";
      }
      buffer_worker_out ($id, 'info', "Failed");
      next PATCHURL
    }
    if ($patchurl =~ /^http:\/\/|^https:\/\/|^ftp:\/\//) {
      buffer_worker_out ($id, 'info', "Trying $patchurl");
      if (!$wget{path}) {
        buffer_worker_out ($id, 'info', "Failed (can't find wget executable)");
        next PATCHURL
      }
      if ($patchurl =~ /^http.*pca-proxy\.cgi/) {
        PROXY: if (download("patch", $pp, "url $patchurl", "$o{patchdir}/$pp.tmp", "")) {
          my $type=filetype("$o{patchdir}/$pp.tmp");
          if ($type ne 'unknown') {
            rename ("$o{patchdir}/$pp.tmp", "$o{patchdir}/$pp.$type");
            buffer_worker_out ($id, 'info', "Done"); $c{dl}++; goto DONE;
          } else {
            buffer_worker_out ($id, 'info', "Failed (unknown file type)");
          }
        } else {
          buffer_worker_out ($id, 'info', "Failed ($wget{error})");
          if (($wget{error} =~ /MOS data missing/) && checksoa()) { goto PROXY }
        }
        unlink "$o{patchdir}/$pp.tmp";
      } else {
        foreach my $ext ('zip','jar','tar.Z','tar') {
          if (download("patch", "$pp.$ext", "url $patchurl", "$o{patchdir}/$pp.$ext", "")) {
            buffer_worker_out ($id, 'info', "Done"); $c{dl}++; goto DONE;
          }
          unlink "$o{patchdir}/$pp.$ext";
        }
        buffer_worker_out ($id, 'info', "Failed ($wget{error})");
      }
      next PATCHURL
    }
    if ($patchurl eq "oracle") {
      buffer_worker_out ($id, 'info', "Trying Oracle");
      if (!checksoa()) {
        buffer_worker_out ($id, 'info', "Failed (no My Oracle Support Account data)");
        next PATCHURL
      }
      if (!$wget{path}) {
        buffer_worker_out ($id, 'info', "Failed (can't find wget executable)");
        next PATCHURL
      }
      if ($wget{proto} ne "https") {
        buffer_worker_out ($id, 'info', "Failed (wget doesn't support HTTPS)");
        next PATCHURL
      }
      my $try=1;
      while ($try <= $o{dltries} ) {
        buffer_worker_out ($id, 'info', "Trying https://$o{ohost}/ ($try/$o{dltries})");
        if (download("patch.zip", $pp, "oracle", "$o{patchdir}/$pp.zip", "")) {
          if (filetype("$o{patchdir}/$pp.zip") ne 'zip') {
            buffer_worker_out ($id, 'info', "Failed (unknown file type)");
          } else {
            buffer_worker_out ($id, 'info', "Done"); $c{dl}++; goto DONE;
          }
        }
        buffer_worker_out ($id, 'info', "Failed ($wget{error})");
        unlink "$o{patchdir}/$pp.zip";
        last if ($wget{error} =~ /You are not entitled to retrieve this content/);
        last if ($wget{error} =~ /Login failed/);
        $try++; if ($try <= $o{dltries}) { sleep ($try*2) }
      }
      next PATCHURL
    }
    out ('info', "Trying $patchurl");
    out ('info', "Failed (unknown type of URL)");
  }
FAIL:
  buffer_worker_out ($id, 'info', "Failed (patch not found)");
  $c{faildl}++;
DONE:
  lock_remove($o{patchdir}, "download.$pp");
}

sub download {
  my $what=$_[0]; my $pp=$_[1]; my $src=$_[2]; my $dstf=$_[3]; my $dstd=$_[4];
  my @out=(); my $srcurl="";

  if ($src =~ /^url\s/) {
    ($src, $srcurl)=(split (/\s/, $src));
    if ($srcurl =~ /\.cgi$/) { $srcurl .= "?" }
    if ($srcurl =~ /[^\/\?=]$/) { $srcurl .= "/" }
  }
  if ($src =~ /^oracle$/i) { $src="oracle" }
  dbg ("src: $src, srcurl: $srcurl");

  my %urls=(
    "pca:url", "${srcurl}pca",
    "xref:url", "${srcurl}patchdiag.xref",
    "xref:oracle", "https://$o{ohost}/reports/patchdiag.xref",
    "readme:url", "${srcurl}README.$pp",
    "readme:oracle", "https://$o{ohost}/readme/README.$pp",
    "patch:url", "${srcurl}$pp",
    "patch.zip:oracle", "https://$o{ohost}/all_unsigned/$pp.zip",
    "status:oracle", "https://support.oracle.com/CSP/login?cmd=status"
  );
  my $cmd="$wget{path}"; my $url;

  foreach my $i (@{$o{wgetopt}}) { $cmd .= " $i" }
  if (($o{debug}) && ($o{threads} > 1)) { $cmd .= " -nv" }
  if ($wget{version} >= 10800) { $cmd .= " --progress=dot:binary" }

  $url=$urls{"$what:$src"};
  if ($what =~ /^patch/) { $what = "patch" } # remove possible zip/tar postfix
  if (($o{force}) && ($url =~ /pca-proxy\.cgi/)) { $url .= ":force" }

  if ($o{wgetproxy}) {
    $cmd .= " --execute http_proxy=$o{wgetproxy}";
    $cmd .= " --execute https_proxy=$o{wgetproxy}";
  }
  if (($what eq "xref") && ($src eq "oracle") && ($o{nocache})) { $cmd .= " --execute cache=off" }
  if ((($url =~ /https:\/\/www.par.univie.ac.at\//) || ($url =~ /https:\/\/getupdates.oracle.com\//) || ($url =~ /https:\/\/support.oracle.com\//)) && ($wget{version} >= 11000)) { $cmd .= " --ca-certificate=$0" }
  if ((($url =~ /https:\/\/getupdates.oracle.com\//) || ($url =~ /https:\/\/support.oracle.com\//)) && ($wget{version} <= 11200)) { $cmd .= " --no-check-certificate" }
  if (($url =~ /https:\/\/getupdates.oracle.com\//) || ($url =~ /https:\/\/support.oracle.com\//)) { $cmd .= " --secure-protocol=TLSv1" }
  if (($what eq "patch") && ($url =~ /pca-proxy\.cgi/)) { $cmd .= " --timeout 3600" }
  if ((($what eq "patch") || ($what eq "readme")) && ($url =~ /pca-proxy\.cgi/)) {
    if ($a{user}) {
      wgetrc_add ("header=X_PCA_USER: $a{user}");
    } elsif ($o{user}) {
      wgetrc_add ("header=X_PCA_USER: $o{user}");
    }
    if ($a{passwd}) {
      wgetrc_add ("header=X_PCA_PASSWD: $a{passwd}");
    } elsif ($o{passwd}) {
      wgetrc_add ("header=X_PCA_PASSWD: $o{passwd}");
    }
  }
  if ((($what eq "patch") || ($what eq "readme") || ($what eq "status")) && ($src eq "oracle")) {
    wgetrc_add ("header=Authorization: Basic " . base64("$a{user}:$a{passwd}"));
  }

  if ($dstf) {
    $cmd .= " -O $dstf";
    if ($what eq "patch") { $p{$pp}{dlfile}="$dstf" } else { $dlfile="$dstf" }
  }
  if ($dstd) {
    $cmd = "cd $dstd; " . $cmd . " -N";
  }
  $cmd .= " \"$url\"";
  dbg ($cmd);
  open (CMD, "$cmd 2>&1 |");
  while (<CMD>) { chomp; dbg ($_); push (@out, $_) }
  close (CMD);
  wgetrc_remove();
  if ($what eq "patch") { $p{$pp}{dlfile}="" } else { $dlfile="" }

  $wget{error}="Unknown Error";
  for my $i (@out) {
    if ($i =~ /Length: 2009.*text\/html/) {
      $wget{error}="Error 401: Login failed";
      unlink ($dstf);
      return 0;
    }
  }
  if (!$? && ($dstd)) { return 1 }
  if (!$? && ($dstf) && (-s $dstf)) { return 1 }
  for my $i (@out) {
    if ($i =~ /401 Unauthorized$/) { $wget{error}="Error 401: Unauthorized" }
    if ($i =~ /401 MOS data missing$/) { $wget{error}="Error 401: MOS data missing" }
    if ($i =~ / ERROR (\d+): (.+).$/) { $wget{error}="Error $1: $2" }
  }
  return 0;
}

sub wgetrc_add {
  if (!$wget{rc}) {
    $wget{rc}= tempfile();
    if ($ENV{HOME} && -f "$ENV{HOME}/.wgetrc") {
      dbg ("wgetrc: found $ENV{HOME}/.wgetrc");
      copy ("$ENV{HOME}/.wgetrc", $wget{rc})
    }
    if ($ENV{WGETRC} && -f $ENV{WGETRC}) {
      dbg ("wgetrc: found $ENV{WGETRC}");
      copy ($ENV{WGETRC}, $wget{rc})
    }
    chmod 0600, $wget{rc};
    if ($ENV{WGETRC}) { $ENV{SAVEWGETRC}=$ENV{WGETRC}; dbg ("SAVEWGETRC: $ENV{WGETRC}") }
    $ENV{WGETRC}=$wget{rc};
  }
  dbg ("Adding to $wget{rc}: $_[0]");
  open (OUT, ">>$wget{rc}"); print OUT "$_[0]\n"; close (OUT);
}

sub wgetrc_remove {
  return unless ($wget{rc});
  dbg ("Removing $wget{rc}");
  unlink ($wget{rc});
  delete $ENV{WGETRC};
  if ($ENV{SAVEWGETRC}) { $ENV{WGETRC}=$ENV{SAVEWGETRC}; dbg ("WGETRC: $ENV{SAVEWGETRC}") }
  $wget{rc}='';
}

sub filetype {
  my $fname=$_[0]; my $buffer;

  open (F, "< $fname") || errx ("Can't open $fname ($!)");
  my $size=read (F, $buffer, 512);
  close (F);

  if ($size != 512) { dbg ("Short file: $fname"); return ('unknown') }
  if (substr($buffer, 257, 5) eq "ustar") { return ('tar') }
  if (substr($buffer, 0, 2) eq "\037\235") { return ('tar.Z') }
  if (substr($buffer, 0, 4) eq "PK\003\004") {
    `$unzip -l $fname META-INF/manifest.mf META-INF/MANIFEST.MF 2>&1`;
    if ($?) { return ('zip') } else { return ('jar') }
  }

  dbg ("Unknown Filetype: $fname");
  return ('unknown');
}

sub statout {
  my $now=(split (/\s+/, (localtime())))[3];
  my $pdur=sec2hms(time()-$timing{pstart});
  my $tdur=sec2hms(time()-$timing{start});
  return "($now/$pdur/$tdur, $c{current}/$c{total}, $c{inst}/$c{skipinst}/$c{failinst})";
}

sub sec2hms {
  my $t=$_[0];

  my $s=$t % 60; $t=($t-$s)/60; my $m=$t % 60; $t=($t-$m)/60; my $h=$t;
  return (sprintf "%02d:%02d:%02d", $h,$m,$s);
}

sub install_patch {
  my $pp=$_[0];
  my ($id, $rev)= split (/-/, $pp);
  my $output;
  my $dfile='';
  my $opt='';

  $patchxdir= tempdir(); chmod 0755, $patchxdir;
  dbg ("patchxdir: $patchxdir");
  $timing{pstart}=time();

  if (-d "$o{patchdir}/$pp") {
    $?= !symlink ("$o{patchdir}/$pp", "$patchxdir/$pp");
  } elsif (-f "$o{patchdir}/$pp.zip") {
    out ('info', "Unzipping patch");
    `$unzip -n $o{patchdir}/$pp.zip -d $patchxdir </dev/null 2>&1`;
    $p{$id}{dfori} && ($dfile= "$o{patchdir}/$pp.zip")
  } elsif (-f "$o{patchdir}/$pp.jar") {
    out ('info', "Unjarring patch");
    `$unzip -n $o{patchdir}/$pp.jar -d $patchxdir </dev/null 2>&1`;
    $p{$id}{dfori} && ($dfile= "$o{patchdir}/$pp.jar")
  } elsif (-f "$o{patchdir}/$pp.tar.Z") {
    out ('info', "Uncompressing patch");
    `cd $patchxdir; $uncompress -c $o{patchdir}/$pp.tar.Z | $tar xf -`;
    $p{$id}{dfori} && ($dfile= "$o{patchdir}/$pp.tar.Z")
  } elsif (-f "$o{patchdir}/$pp.tar") {
    out ('info', "Untarring patch");
    `cd $patchxdir; $tar xf $o{patchdir}/$pp.tar`;
    $p{$id}{dfori} && ($dfile= "$o{patchdir}/$pp.tar")
  } else {
    rmdir $patchxdir; $patchxdir="";
    $c{failinst}++; out ('info', "Failed - missing patch file " . statout());
    return;
  }
  if (($?) || (! -d "$patchxdir/$pp")) {
    rmtree ($patchxdir); $patchxdir="";
    $c{failinst}++; out ('info', "Failed " . statout());
    return;
  }
  my $readme= "$patchxdir/$pp/README.$pp";
  my $patchinfo= "$patchxdir/$pp/patchinfo";

  if ($o{safe}) {
    out ('info', "Checking files for safe patch installation");
    if (!verify_files($id, $readme)) {
      $c{failinst}++; out ('info', "Failed - file verification " . statout());
      rmtree ($patchxdir); $patchxdir="";
      return;
    }
  }

  # Do we need a reboot?
  my $p_b=0; my $p_bi=0; my $p_c=0; my $p_ci=0;
  if (-f $patchinfo) {
    open(PATCHINFO,$patchinfo) || errx ("Can't open $patchinfo ($!)");
    dbg ("Checking for reboot/reconfig in patchinfo");
    while (<PATCHINFO>) {
      if (/PATCH_PROPERTIES=.*reconfigimmediate/) { $p_ci=1; last }
      if (/PATCH_PROPERTIES=.*rebootimmediate/) { $p_bi=1; last }
      if (/PATCH_PROPERTIES=.*reconfigafter/) { $p_c=1; last }
      if (/PATCH_PROPERTIES=.*rebootafter/) { $p_b=1; last }
    }
    close PATCHINFO;
  } elsif (-f $readme) {
    open(README,$readme) || errx ("Can't open $readme ($!)");
    dbg ("Checking for reboot/reconfig in README");
    while(<README>) {
      if (/Reconfig.*immediate.*after.*install/) { $p_ci=1; last }
      if (/Reboot.*immediate.*after.*install/) { $p_bi=1; last }
      if (/Reconfig.*after.*install/) { $p_c=1; last }
      if (/Reboot.*after.*install/) { $p_b=1; last }
    }
    close README;
  }

  # If the patchadd command doesn't exist, try installpatch, which
  # comes with patches for Solaris <= 2.5.1.
  (-x $o{patchadd}) || ($o{patchadd}="$patchxdir/$pp/installpatch");
  (-x $o{patchadd}) || errx ("Can't execute patchadd/installpatch");

  # Sun Studio 11 patches on Solaris 10 must be installed with -G
  # Patches 119254-34 and 119255-34 fix this in patchadd
  my ($major, $minor) = split (/\./, $u{osrel});
  if (($minor == 10) && ($p{$id}{synopsis} =~ /^Sun Studio 11/) && (!$o{currentzone})) {
    if (!($p{119254}{irev} ge '34') && !($p{119255}{irev} ge '34')) {
      dbg ("Adding -G to patchadd for Sun Studio 11 on Solaris 10");
      $opt .= "-G ";
    }
  }
  # Ignore currentzone option on Solaris <= 9
  ($minor <= 9) && ($o{currentzone}=0);

  if ($o{noreboot} && ($p_ci || $p_bi || $p_c || $p_b)) {
    $c{skipinst}++; out ('info', "Skipped - noreboot " . statout());
    rmtree ($patchxdir); $patchxdir="";
    return;
  }
  if ($o{pretend}) {
    $c{skipinst}++; out ('info', "Skipped - pretend " . statout());
  } else {
    lock_create($o{tmpdir}, "install", 1) || errx ("Another instance of pca is installing patches right now");
    $o{currentzone} && ($opt .= "-G ");
    if (($o{nobackup} =~ /all/) || ($p{$id}{nobackup} eq "00") || ($p{$id}{nobackup} eq $p{$id}{crev})) { $opt .= "-d " }
    $o{backdir} && ($opt .= "-B $o{backdir} ");
    out ('info', "Running patchadd");
    dbg ("Starting patchadd at " . localtime);
    dbg ("$o{patchadd} $o{root} $opt $patchxdir/$pp");
    $SIG{INT}='IGNORE';
    open (CMD, "$o{patchadd} $o{root} $opt $patchxdir/$pp </dev/null 2>&1 |");
    while (<CMD>) { $output .= $_; chomp; dbg ($_) }
    close (CMD);
    $SIG{INT}=\&handler;
    my $rc=$?;
    lock_remove($o{tmpdir}, "install");
    if ($rc) {
      out ('info', "\n$output") unless ($o{debug});
      $rc /= 256; out ('info', "Failed (exit code $rc)\n$!");
      rmtree ($patchxdir); $patchxdir="";
      log_msg("Failed to install patch $pp ($p{$id}{synopsis}) rc=$rc");
      $c{failinst}++; out ('info', "Failed " . statout());
      return;
    }
    $c{inst}++; out ('info', "Successful " . statout());
    $dfile && unlink ($dfile);
    my $msg="Installed patch $pp ($p{$id}{synopsis})";
    $o{root} && ($msg .= " ($o{root})");
    log_msg($msg);
    if ($p_ci || $p_c) {
      my $r=''; if ($o{root}) { $r=$o{root}; $r =~ s/-R // }
      if (! -f "$r/reconfigure") {
        out ('info', "Creating $r/reconfigure");
        open (F, ">$r/reconfigure"); close (F);
      }
    }
  }
     if ($p_ci) { out ('info', "Reconfig required"); $c{p_ci}++ }
  elsif ($p_bi) { out ('info', "Reboot required"); $c{p_bi}++ }
  elsif ($p_c ) { out ('info', "Reconfig recommended"); $c{p_c}++ }
  elsif ($p_b ) { out ('info', "Reboot recommended"); $c{p_b}++ }
  rmtree ($patchxdir); $patchxdir="";
}

sub proxy {
  my $f=$o{proxy};
  my $odir;

  dbg ("Requested file: $f");
  if ($f =~ /^patchdiag.xref$/) {
    $o{xrefown}=1; $odir=$o{xrefdir};
    if ($o{pforce}) { unlink ("$odir/$f") }
    get_current_xref();
  }
  if ($f =~ /^README\.\d{6}-\d{2}$/) {
    my $pp=$f; $pp =~ s/^.*(\d{6}-\d{2}).*$/$1/; $odir=$o{patchdir};
    if ($o{pforce}) { unlink ("$odir/$f") }
    if (! -f "$odir/$f") {
      my $rtmp=get_readme ($pp);
      if ($rtmp) {
        copy ($rtmp, "$odir/$f");
        unlink ($rtmp);
      }
    }
  }
  # Deprecated
  if ($f =~ /^\d{6}-\d{2}\.(zip|jar|tar|tar\.Z)$/) {
    my $pp=$f; $pp =~ s/^.*(\d{6}-\d{2}).*$/$1/; $odir=$o{patchdir};
    if ($o{pforce}) { unlink ("$odir/$f") }
    download_patch($pp);
  }
  if ($f =~ /^\d{6}-\d{2}$/) {
    $odir=$o{patchdir};
    if ($o{pforce}) { unlink ("$odir/$f.zip", "$odir/$f.jar", "$odir/$f.tar", "$odir/$f.tar.Z") }
    download_patch($f);
    (-f "$odir/$f.zip") && ($f="$f.zip");
    (-f "$odir/$f.jar") && ($f="$f.jar");
    (-f "$odir/$f.tar") && ($f="$f.tar");
    (-f "$odir/$f.tar.Z") && ($f="$f.tar.Z");
  }
  if ($f =~ /^pca$/) {
    $odir=$o{patchdir};
    if ($o{pforce}) { unlink ("$odir/$f") }
    if ($o{pcaurl} =~ /^http.*pca-proxy\.cgi/) {
      download('pca', '', "url $o{pcaurl}", "$odir/pca", "");
    } else {
      download('pca', '', "url $o{pcaurl}", "", $odir);
    }
  }

  if (-f "$odir/$f") {
    ($f =~ /patchdiag.xref/) && print "Content-type: text/plain\n";
    ($f =~ /README/) && print "Content-type: text/plain\n";
    ($f =~ /\.zip$/) && print "Content-type: application/zip\n";
    ($f =~ /\.jar$/) && print "Content-type: application/zip\n";
    ($f =~ /\.tar$/) && print "Content-type: application/x-tar\n";
    ($f =~ /\.tar.Z$/) && print "Content-type: application/x-compress\n";
    ($f =~ /^pca$/) && print "Content-type: text/plain\n";

    use POSIX qw(strftime);
    my ($size,$mtime)=(stat("$odir/$f"))[7,9];
    print "Last-Modified: " . strftime("%a, %d %b %Y %H:%M:%S +0000", gmtime($mtime)) . "\n";
    print "Content-length: $size\n\n";

    open (F, "<$odir/$f"); read (F, my $content, $size); close (F);
    print $content;
  } else {
    errx ("404 $f not found");
  }
  exit $xval;
}

sub checksoa {
  lock %a;  # prevent simultaneous access to checksoa() if multithreaded
  if(!$a{transcribed}) {
    $a{user}=$o{user};
    $a{passwd}=$o{passwd};
    $a{asked}=0;
    $a{transcribed}=1;
  }
  # If there is no MOS data available in proxy mode, fail immediately
  if ($o{proxy} && (!$a{user} || !$a{passwd})) { errx ("401 MOS data missing") }

  if (!$a{asked}) {
    my $uask=0;
    $a{asked}=1;

    # If user is not set and not set to "dontask", ask for it
    # 2011/09/30: Deprecated, removed from documentation
    if ($a{user} eq "dontask") {
      $a{user}="";
    } elsif (!$a{user}) {
      print "\nPlease enter My Oracle Support Account User: ";
      $a{user}=<STDIN>; $a{user} && chomp($a{user});
      $uask=1;
    }
    # If user (but not passwd) is set, ask for passwd
    if ($a{user} && !$a{passwd}) {
      system "stty -echo"; $sttyset=1;
      $uask || print "\n";
      print "Please enter My Oracle Support Account Password";
      if ($uask) { print ": " } else { print " for $a{user}: " }
      $a{passwd}=<STDIN>; $a{passwd} && chomp($a{passwd});
      print "\n\n";
      system "stty echo"; $sttyset=0;
    }
  }
  if ($a{user} && $a{passwd}) { return (1) } else { return (0) }
}

sub supplevel {
  my %levels=(
    "OS", "Solaris patches and updates",
    "PUB", "Oracle Open Office/StarOffice and patch utilities",
    "SW", "Existing Oracle software and Sun middleware",
    "FMW", "Firmware, drivers, bios, system controller software, ALOM/ILOM, diagnostics",
    "EXS", "EOL Oracle Software",
    "VIN", "Solaris 8"
  );
  my $status=tempfile();

  if (!$o{debug}) {
    out ('info', "DEPRECATED: Oracle broke the interface to query this information");
    exit $xval;
  }
  out ('info', "Determining MOS Support Levels\n");
  if (checksoa()) {
    if (download('status', '', 'oracle', $status, '')) {
      open (STATUS, "<$status");
      while (<STATUS>) {
        foreach my $code (keys (%levels)) {
          ($_ =~ /priv code="$code"/) && out ('info', "$code: $levels{$code}");
        }
      }
      close (STATUS);
      unlink ($status);
    } else { out ('stderr', "Failed ($wget{error})") }
  } else { out ('stderr', "Failed (no My Oracle Support Account data)") }
  exit $xval;
}

sub check_prerequisites {
  # Must be root to install patches
  if ($o{install} && ($< != 0) && !$o{pretend} && !$o{norootchk}) {
    errx ("You must be root to install patches");
  }
  if ($o{install} && $o{safe} && !$o{proxy} && ($< != 0) && !$o{norootchk}) {
    errx ("You must be root to use safe mode");
  }

  # Set umask (esp. for patchxdir)
  umask (0022);

  # Check for wget executable
  my $found='';
  foreach my $i (split (/ /, $o{wget})) {
    if (-f $i && -x $i) {
      $found=$i
    } elsif (-d $i && -x "$i/wget") {
      $found="$i/wget"
    } else {
      next
    }
    if (!open (W, "$found --version 2>&1 |")) { dbg ("$found: cannot execute"); next }
    my $v=<W>; close (W); chomp $v;
    # A bug in wget 1.13.3 makes it return 3 instead of 0
    my $rc=$?/256;
    if (($rc != 0) && ($rc != 3)) { errx ("$v (exit code: $rc)") }
    $v =~ s/^GNU Wget ([\d\.]*).*$/$1/; my ($v1, $v2, $v3) = split (/\./, $v);
    my $version=$v1*10000 + $v2*100; $v3 && ($version += $v3);
    my $proto='http';
    open (W, "$found --help |"); while (<W>) { ($_ =~ /HTTPS/) && ($proto='https') } close (W);
    if ($version == "11303") {
      dbg ("wget 1.13.3 is buggy: impossible to check for HTTPS support");
      $proto='https';
    }
    dbg ("Found $found ($v, $version, $proto)");
    if ((length($proto) > length($wget{proto})) || (($version > $wget{version}) && (length($proto) >= length($wget{proto})))) {
      $wget{path}=$found; $wget{version}=$version; $wget{proto}=$proto;
    }
  }
  $wget{path} && dbg ("Using $wget{path}");

  # Get patchdiag.xref location
  $input{xref}="$o{xrefdir}/patchdiag.xref";

  # Check patch download directory
  (-d $o{patchdir}) || errx ("Can't find patch directory $o{patchdir}");

  # Check for pager
  foreach my $i (split (/ /, $pager)) {
    if (-f $i && -x $i) { $pager=$i; last }
  }
  $ENV{PAGER} && ($pager=$ENV{PAGER});

  # Check for valid prefix in $fromfiles and set input files/commands
  if ($o{fromfiles}) {
    if (-f "$o{fromfiles}/sysconfig/uname-a.out") {
      $input{pkginfo}= "<$o{fromfiles}/patch+pkg/pkginfo-l.out";
      $input{showrev}= "<$o{fromfiles}/patch+pkg/showrev-p.out";
      $input{uname}  = "<$o{fromfiles}/sysconfig/uname-a.out";
    } elsif (-f "$o{fromfiles}uname.out") {
      $input{pkginfo}= "<$o{fromfiles}pkginfo.out";
      $input{showrev}= "<$o{fromfiles}showrev.out";
      $input{uname}  = "<$o{fromfiles}uname.out";
    } elsif (-f "$o{fromfiles}/uname.out") {
      $input{pkginfo}= "<$o{fromfiles}/pkginfo.out";
      $input{showrev}= "<$o{fromfiles}/showrev.out";
      $input{uname}  = "<$o{fromfiles}/uname.out";
    } else {
      errx ("Can't find pkginfo/showrev/uname output with prefix $o{fromfiles}");
    }
    dbg ("Using $o{fromfiles} as prefix to read .out files");
  } else {
    $input{pkginfo}= "$pkginfo -x $o{root} |";
    foreach my $i (split (/ /, $uname)) {
      if (-f $i && -x $i) { $uname=$i; last }
    }
    dbg ("Found $uname");
    $input{uname}  = "$uname -a |";
  }

  # Set default locale for forks
  $ENV{LC_ALL}='C';

  # Make sure that any request to thread is sane
  if (!$Config{useithreads} || $o{threads} < 2 || !($o{download} || $o{install})) {
    dbg ("Prerequisites for threads not met, setting threads to 0");
    $o{threads} = 0;
  }
}

sub import_threads {
  return unless ($o{threads} > 1);

  eval { require threads; require threads::shared; require Thread::Queue; };
  if (!$@) {
    dbg ("Thread modules passed require, importing");
    BEGIN { $^W = 0 }
    threads->import;
    BEGIN { $^W = 1 }
    threads::shared->import;
    Thread::Queue->import;
    $queue = new Thread::Queue;
    share(\%a);
    share(\%c);
    share(\$download_start);
    share(\%locks);
  }
  else {
    dbg ("Thread modules did not pass require");
    $o{threads} = 0;
  }
}

sub verify_files {
  my $id=$_[0]; my $readme=$_[1]; my @files=(); my %wl;

  # All
  $wl{all}="/etc/name_to_major /etc/driver_aliases /etc/driver_classes /etc/minor_perm /etc/security/exec_attr";
  # 8/SPARC
  $wl{108725}="/kernel/drv/st.conf";
  $wl{108968}="/etc/rmmount.conf /etc/vold.conf";
  $wl{108999}="/etc/pam.conf";
  $wl{109077}="/etc/security/auth_attr /etc/security/prof_attr";
  $wl{109134}="/etc/security/auth_attr /etc/security/prof_attr";
  $wl{109695}="/etc/smartcard/opencard.properties";
  $wl{109766}="/usr/openwin/lib/locale/ja/X11/fonts/TT/fonts.alias";
  $wl{109887}="/etc/smartcard/ocf.classpath";
  $wl{110369}="/etc/iu.ap";
  $wl{110386}="/etc/security/auth_attr /etc/security/prof_attr";
  $wl{110615}="/etc/mail/main.cf /etc/mail/subsidiary.cf";
  $wl{110896}="/etc/inet/inetd.conf";
  $wl{112438}="/etc/devlink.tab";
  $wl{112663}="/usr/openwin/server/etc/OWconfig";
  $wl{114542}="/usr/openwin/lib/X11/fonts/TrueType/ttmap/ttmaps.dir /usr/openwin/lib/X11/fonts/encodings/encodings.dir";
  $wl{116973}="/etc/apache/mime.types";
  $wl{117518}="/usr/openwin/lib/X11/fonts/F3bitmaps/fonts.dir";
  $wl{128624}="/etc/default/login /etc/nsswitch.conf /etc/pam.conf";
  # 9/SPARC
  $wl{112233}="/etc/iu.ap";
  $wl{112874}="/etc/name_to_sysnum /etc/security/crypt.conf /etc/security/policy.conf";
  $wl{112908}="/etc/krb5/krb5.conf";
  $wl{112954}="/kernel/drv/uata.conf";
  $wl{113073}="/etc/inet/inetd.conf";
  $wl{113085}="/usr/openwin/lib/X11/fonts/TrueType/ttmap/ttmaps.dir /usr/openwin/lib/X11/fonts/encodings/encodings.dir";
  $wl{113096}="/usr/openwin/server/etc/OWconfig";
  $wl{113471}="/usr/bin/cputrack";
  $wl{113575}="/etc/mail/main.cf /etc/mail/subsidiary.cf";
  $wl{114320}="/usr/openwin/server/etc/OWconfig";
  $wl{114352}="/etc/inet/inetd.conf";
  $wl{123184}="/usr/openwin/lib/X11/fonts/TrueType/ttmap/ttmaps.dir /usr/openwin/lib/X11/fonts/encodings/encodings.dir";
  $wl{115336}="/etc/security/auth_attr /etc/security/prof_attr";
  # 9/x86
  $wl{114137}="/etc/mail/main.cf /etc/mail/subsidiary.cf";
  $wl{114353}="/etc/inet/inetd.conf";
  $wl{115168}="/etc/krb5/krb5.conf";
  $wl{122300}="/etc/rc0.d/K05volmgt /etc/rc1.d/K05volmgt /etc/rc2.d/K05volmgt /etc/rc3.d/S81volmgt /etc/rcS.d/K05volmgt /etc/security/audit_class /etc/security/audit_event /kernel/drv/sd.conf /etc/ssh/sshd_config";
  $wl{115337}="/etc/security/auth_attr /etc/security/prof_attr";
  # 10/SPARC
  $wl{116298}="/usr/bin/wscompile /usr/bin/wsdeploy";
  $wl{118666}="/etc/.java/.systemPrefs/.system.lock /etc/.java/.systemPrefs/.systemRootModFile";
  $wl{118717}="/usr/openwin/server/etc/OWconfig";
  $wl{118833}="/etc/logindevperm /etc/security/prof_attr /etc/vold.conf /etc/security/auth_attr";
  $wl{119130}="/kernel/drv/fp.conf /kernel/drv/qlc.conf";
  $wl{119252}="/etc/default/kbd /etc/default/nfs";
  $wl{119313}="/etc/security/auth_attr /etc/security/prof_attr";
  $wl{119757}="/etc/inet/services";
  $wl{120011}="/etc/inet/hosts /etc/inet/ipnodes /etc/inet/services /etc/nscd.conf /etc/security/auth_attr /etc/security/prof_attr /etc/default/dhcpagent /etc/security/device_policy /etc/iu.ap";
  $wl{120185}="/opt/staroffice8/share/config/javasettingsunopkginstall.xml";
  $wl{120346}="/etc/hba.conf";
  $wl{120410}="/etc/gtk-2.0/gtk.immodules /etc/sparcv9/gtk-2.0/gtk.immodules";
  $wl{120460}="/etc/gtk-2.0/gtk.immodules /etc/sparcv9/gtk-2.0/gtk.immodules";
  $wl{121308}="/usr/sadm/lib/smc/policy/smcconsole.policy";
  $wl{121430}="/etc/default/lu";
  $wl{122212}="/etc/gconf/gconf.xml.defaults/apps/panel/default_setup/general/%gconf.xml";
  $wl{124393}="/etc/security/auth_attr /etc/security/prof_attr";
  $wl{125166}="/kernel/drv/qlc.conf";
  $wl{127127}="/etc/krb5/krb5.conf /etc/logadm.conf /etc/pam.conf /etc/security/audit_warn /etc/security/auth_attr /etc/security/prof_attr /etc/shadow /etc/user_attr /kernel/drv/mpt.conf";
  $wl{127755}="/etc/logadm.conf";
  $wl{128402}="/etc/default/kbd";
  $wl{137093}="/etc/logindevperm";
  $wl{137137}="/etc/vfstab";
  $wl{137274}="/etc/mnttab";
  $wl{137048}="/platform/sun4u-us3/lib/libc_psr.so.1 /platform/sun4u-us3/lib/sparcv9/libc_psr.so.1";
  $wl{141444}="/etc/power.conf /etc/security/device_policy";
  $wl{144188}="/kernel/drv/emlxs.conf";
  $wl{142933}="/platform/sun4u/failsafe";
  $wl{142909}="/etc/security/auth_attr /etc/security/device_policy /etc/security/prof_attr /kernel/drv/ixgbe.conf";
  $wl{146673}="/etc/security/auth_attr /etc/security/prof_attr";
  $wl{146232}="/etc/ima.conf /etc/hba.conf";
  $wl{146489}="/kernel/drv/qlc.conf";
  $wl{144500}="/etc/apache/httpd-standalone-ipp.conf /etc/crypto/kcf.conf /etc/inet/sock2path /etc/logadm.conf /etc/pam.conf /etc/ssh/sshd_config /kernel/drv/scsi_vhci.conf";
  $wl{147268}="/etc/passwd /etc/shadow /etc/group /etc/ftpd/ftpusers";
  $wl{147440}="/etc/ftpd/ftpusers /etc/shadow /etc/passwd /etc/group";
  $wl{148165}="/etc/security/policy.conf";
  $wl{147673}="/etc/user_attr";
  $wl{146399}="/usr/openwin/server/etc/OWconfig";
  $wl{147147}="/etc/default/nfs /etc/ftpd/ftpusers /etc/passwd /etc/shadow /etc/usb/config_map.conf";
  $wl{148027}="/etc/security/auth_attr /etc/security/prof_attr";
  $wl{149173}="/kernel/drv/emlxs.conf";
  $wl{149175}="/kernel/drv/qlc.conf";
  $wl{147143}="/etc/ima.conf /etc/hba.conf";
  $wl{150525}="/etc/shadow";
  $wl{148104}="/etc/ssh/sshd_config";
  # 10/x86
  $wl{118855}="/etc/logindevperm /etc/security/prof_attr /etc/vold.conf /lib/libc.so.1 /etc/security/device_policy /etc/ipf/pfil.ap /boot/solaris/devicedb/master";
  $wl{119131}="/kernel/drv/fp.conf /kernel/drv/qlc.conf";
  $wl{119253}="/etc/default/kbd /etc/default/nfs";
  $wl{119314}="/etc/security/auth_attr /etc/security/prof_attr";
  $wl{119758}="/etc/inet/services";
  $wl{120012}="/boot/solaris/bootenv.rc /boot/solaris/devicedb/master /etc/default/dhcpagent /etc/inet/hosts /etc/inet/ipnodes /etc/inet/services /etc/nscd.conf /etc/security/auth_attr /etc/security/device_policy /etc/security/prof_attr";
  $wl{120186}="/opt/staroffice8/share/config/javasettingsunopkginstall.xml";
  $wl{120273}="/etc/sma/snmp/snmpd.conf";
  $wl{120347}="/etc/hba.conf";
  $wl{120411}="/etc/gtk-2.0/gtk.immodules /etc/amd64/gtk-2.0/gtk.immodules";
  $wl{120461}="/etc/gtk-2.0/gtk.immodules /etc/amd64/gtk-2.0/gtk.immodules";
  $wl{121309}="/usr/sadm/lib/smc/policy/smcconsole.policy";
  $wl{121431}="/etc/default/lu";
  $wl{122213}="/etc/gconf/gconf.xml.defaults/apps/panel/default_setup/general/%gconf.xml";
  $wl{124394}="/etc/security/auth_attr /etc/security/prof_attr";
  $wl{125165}="/kernel/drv/qlc.conf";
  $wl{125216}="/etc/wgetrc";
  $wl{127128}="/etc/krb5/krb5.conf /etc/logadm.conf /etc/pam.conf /etc/security/audit_warn /etc/security/auth_attr /etc/security/prof_attr /etc/shadow /etc/user_attr /kernel/drv/mpt.conf";
  $wl{127756}="/etc/logadm.conf";
  $wl{137094}="/etc/logindevperm";
  $wl{137138}="/etc/vfstab /lib/libc.so.1";
  $wl{137275}="/etc/mnttab";
  $wl{138270}="/etc/security/device_policy";
  $wl{141445}="/etc/power.conf /etc/security/device_policy /kernel/drv/sd.conf /lib/libc.so.1";
  $wl{144189}="/kernel/drv/emlxs.conf";
  $wl{142934}="/boot/amd64/x86.miniroot-safe /boot/x86.miniroot-safe";
  $wl{142910}="/etc/iu.ap /etc/security/auth_attr /etc/security/device_policy /etc/security/prof_attr /etc/ssh/sshd_config /kernel/drv/ixgbe.conf /lib/libc.so.1";
  $wl{144537}="/lib/libc.so.1";
  $wl{146674}="/etc/security/auth_attr /etc/security/prof_attr";
  $wl{146233}="/etc/ima.conf /etc/hba.conf";
  $wl{146490}="/kernel/drv/qlc.conf";
  $wl{144501}="/etc/apache/httpd-standalone-ipp.conf /etc/crypto/kcf.conf /etc/inet/sock2path /etc/logadm.conf /etc/pam.conf /etc/ssh/sshd_config /kernel/drv/scsi_vhci.conf /lib/libc.so.1";
  $wl{147269}="/etc/passwd /etc/shadow /etc/group /etc/ftpd/ftpusers";
  $wl{147714}="/lib/libc.so.1";
  $wl{147441}="/etc/ftpd/ftpusers /etc/shadow /etc/passwd /etc/group /lib/libc.so.1";
  $wl{148166}="/etc/security/policy.conf";
  $wl{147674}="/etc/user_attr";
  $wl{147148}="/etc/default/nfs /etc/ftpd/ftpusers /etc/shadow /etc/usb/config_map.conf";
  $wl{148028}="/etc/security/auth_attr /etc/security/prof_attr";
  $wl{149174}="/kernel/drv/emlxs.conf";
  $wl{149176}="/kernel/drv/qlc.conf";
  $wl{147144}="/etc/ima.conf /etc/hba.conf";
  $wl{150526}="/etc/shadow";
  $wl{148105}="/etc/ssh/sshd_config";

  (-f $readme) || return (1);
  open (README, "<$readme") || errx ("Can't open $readme ($!)");

  FILE: while (<README>) {
    next if ($_ !~ /Files included with this patch:/);
    LINE: while (<README>) {
      chomp;
      next if (/^$/);
      last FILE if (! /\//);
      next if (/ELF/); # Ignore files with "ELF" in pathname - pkgchk bug
      s/\s+SUNW\w*//;
      s/\s+\(deleted\)//;
      s/\s+\<deleted\>//;
      s/\(deleted\)$//;
      s/\(deleted file\)$//;
      s/^\s+//;
      s/^/\// unless /^\//;

      foreach my $i (split (/ /, $wl{all})) { ($_ eq $i) && next LINE; }
      if ($wl{$id}) {
        foreach my $i (split (/ /, $wl{$id})) { ($_ eq $i) && next LINE; }
      }
      # Ignore directory with generated files (119906/119907)
      if ($_ =~ /^\/usr\/share\/mime\//) { next LINE }

      push (@files, $_);
    }
  }
  close (README);
  dbg ("Number of files to check: ", $#files+1);
  ($#files == -1) && return (1);

  # Workaround for problem with DAP and turbo-packaging
  my $root=$o{root};
  if (-f "/var/run/.patchSafeMode/.patch.safemode.lock") {
    $root='-R /var/run/.patchSafeMode/root';
  }
  # pkgchk has a limit of 1024 pathnames
  my @tfiles=@files; my $out='';
  while ($#tfiles != -1) {
    my $fc=$#tfiles;
    ($fc >= 1023) && ($fc=1023);
    my $pfile= tempfile();
    open (PFILE, ">$pfile") || errx ("Can't open $pfile ($!)");
    foreach my $f (@tfiles[0..$fc]) { print PFILE "$f\n" }
    close PFILE;
    dbg ("$pkgchk $root -q -i $pfile");
    $out .= `$pkgchk $root -q -i $pfile 2>&1`;
    unlink $pfile;
    for (0..1023) { shift @tfiles; }
  }
  ($out) || return (1);

  if ($out =~ /file size |file cksum |pathname |pkgchk: ERROR/) {
    print "failed file verification:\n\n$out";
    return (0);
  }
  return (1);
}

sub set_extra_req {
  $x{113039}=$x{113040}=$x{113041}=$x{113042}=$x{113043}=$x{113044}=$x{114476}="rpkg=SUNWsan";
  $x{111095}=$x{111096}=$x{111413}=$x{111846}=$x{114475}="rpkg=SUNWsan";
  $x{114046}=$x{119209}="rosrel=5.8";
  $x{114049}=$x{114050}=$x{119211}=$x{119212}="rosrel=5.9";
  $x{117765}=$x{117766}="rosrel=5.8"; $x{117767}=$x{117768}="rosrel=5.9";
  $x{114644}=$x{114645}=$x{114646}=$x{114647}=$x{114648}=$x{114649}="rosrel=5.8";
  $x{114650}=$x{114651}=$x{114652}=$x{114653}="rosrel=5.8";
  $x{114816}=$x{114817}=$x{115780}=$x{115781}=$x{117520}=$x{117521}="rosrel=5.8";
  $x{114686}=$x{114687}=$x{114688}=$x{114689}="rosrel=5.9";
  $x{114690}=$x{114691}=$x{114692}=$x{114693}=$x{114694}=$x{114695}="rosrel=5.9";
  $x{114818}=$x{114819}=$x{115782}=$x{115783}=$x{117526}=$x{117527}="rosrel=5.9";
  $x{114255}="rarch=sparc"; $x{114256}="rarch=i386";
  $x{115328}="rosrel=5.8";
  $x{115342}="rosrel=5.9";
  $x{115343}="rosrel=5.9";
  $x{119346}="rosrel=5.10";
  $x{115766}=$x{120879}=$x{120954}="rarch=sparc";
  $x{120091}=$x{120880}=$x{120955}="rarch=i386";
  $x{119300}="rosrel=5.8"; $x{119301}="rosrel=5.9"; $x{119302}="rosrel=5.10";
  $x{113434}="rpkg=SUNWwbsup";
  $x{123200}="rosrel=5.8"; $x{123201}="rosrel=5.9"; $x{123202}="rosrel=5.10";
  $x{119527}=$x{119530}=$x{119325}="rarch=sparc";
  $x{119528}=$x{119531}=$x{119326}="rarch=i386";
  $x{127498}=$x{127499}="rosrel=5.8";
  $x{136986}=$x{136987}="rosrel=5.8";
  $x{125950}=$x{125951}="rosrel=5.9";
  $x{147673}=$x{147674}="rosrel=5.10";
  $x{123827}="rosrel=5.8"; $x{123828}="rosrel=5.9"; $x{123829}="rosrel=5.10";
  $x{117784}=$x{118195}=$x{118263}=$x{118950}=$x{123254}="rarch=sparc";
  $x{117785}=$x{118196}=$x{118264}=$x{118951}=$x{124590}="rarch=i386";
  $x{126356}="rarch=sparc"; $x{126357}="rarch=i386";
  $x{117429}="rosrel=5.9";
  $x{118386}="rosrel=5.6"; $x{118387}="rosrel=5.7"; $x{118388}="rosrel=5.8"; $x{118389}="rosrel=5.9";
  $x{118828}="rosrel=5.8"; $x{118829}="rosrel=5.9";
  $x{118836}="rosrel=5.6"; $x{118837}="rosrel=5.7"; $x{118838}="rosrel=5.8";
  $x{118839}="rosrel=5.9"; $x{118840}="rosrel=5.9";
  $x{120376}="rosrel=5.6"; $x{120377}="rosrel=5.7"; $x{120378}="rosrel=5.8"; $x{120379}="rosrel=5.9";
  $x{124689}="rosrel=5.8"; $x{124690}="rosrel=5.9";
  $x{111857}="rosrel=5.8"; $x{114176}="rosrel=5.9";
  $x{125445}="rosrel=5.9"; $x{125446}="rosrel=5.10";
  $x{127553}="rarch=sparc"; $x{127554}="rarch=i386";
  $x{121708}="rosrel=5.8"; $x{121709}="rosrel=5.9"; $x{121710}="rosrel=5.10";
  $x{115835}=$x{115836}="rpkg=SUNWgscr";
  $x{125276}="rarch=sparc";
  $x{116413}="rplatform=SUNW,Sun-Fire-15000";
  $x{125277}="rosrel=5.9:rarch=i386";
  $x{125278}="rosrel=5.10:rarch=i386";
  $x{124480}="rosrel=5.9:rarch=sparc";
  $x{124481}="rosrel=5.10:rarch=sparc";
  $x{124482}="rosrel=5.10:rarch=i386";
  $x{119380}="rosrel=5.8";
  $x{110936}=$x{110971}="rosrel=5.6";
  $x{110937}=$x{110972}="rosrel=5.7";
  $x{113120}="rosrel=5.6"; $x{113121}="rosrel=5.7"; $x{113122}="rosrel=5.8"; $x{113123}="rosrel=5.9";
  $x{118386}="rosrel=5.6"; $x{118387}="rosrel=5.7"; $x{118388}="rosrel=5.8"; $x{118389}="rosrel=5.9";
  $x{118828}="rosrel=5.8"; $x{118829}="rosrel=5.9";
  $x{118836}="rosrel=5.6"; $x{118837}="rosrel=5.7"; $x{118838}="rosrel=5.8"; $x{118839}="rosrel=5.9";
  $x{127680}="rosrel=5.8"; $x{127681}=$x{127682}="rosrel=5.9"; $x{143323}=$x{143324}="rosrel=5.10";
  $x{138550}="rosrel=5.8"; $x{138551}=$x{138552}="rosrel=5.9"; $x{138553}=$x{138554}="rosrel=5.10";
  $x{123919}="rosrel=5.7"; $x{123920}="rosrel=5.8"; $x{123921}="rosrel=5.9"; $x{123923}="rosrel=5.10";
  $x{139548}="rarch=sparc"; $x{139549}="rarch=i386";
  $x{116687}="rosrel=5.7"; $x{116688}="rosrel=5.8"; $x{116689}="rosrel=5.9";
  $x{120108}="rosrel=5.7"; $x{120109}="rosrel=5.8"; $x{120110}="rosrel=5.9";
  $x{119300}="rosrel=5.8"; $x{119301}="rosrel=5.9"; $x{119302}="rosrel=5.10";
  $x{123200}="rosrel=5.8"; $x{123201}="rosrel=5.9"; $x{123202}="rosrel=5.10";
  $x{123827}="rosrel=5.8"; $x{123828}="rosrel=5.9"; $x{123829}="rosrel=5.10";
  $x{136799}="rosrel=5.9"; $x{136800}="rosrel=5.10";
  $x{140993}="rarch=sparc"; $x{140994}="rarch=i386";
  $x{139610}="rosrel=5.8"; $x{139611}="rosrel=5.9";
  $x{143075}="rosrel=5.8"; $x{143076}="rosrel=5.9"; $x{143077}="rosrel=5.9:rarch=i386"; $x{143078}="rosrel=5.10"; $x{143079}="rosrel=5.10:rarch=i386";
  $x{143310}="rosrel=5.8"; $x{143311}=$x{143312}="rosrel=5.9"; $x{143313}=$x{143314}="rosrel=5.10";
  $x{143320}="rosrel=5.8"; $x{143321}=$x{143322}="rosrel=5.9"; $x{143323}="rosrel=5.10"; $x{143324}="rosrel=5.10:rarch=i386";
  $x{142633}="rosrel=5.9"; $x{142634}="rosrel=5.10";
  $x{119303}="rosrel=5.8"; $x{119304}="rosrel=5.9"; $x{119305}="rosrel=5.10";
  $x{147416}="rarch=sparc"; $x{147419}="rarch=i386";
}

sub chk_extra_req {
  my $id=$_[0];
  my ($major, $minor) = split (/\./, $u{osrel});

  if (exists $x{$id}) {
    foreach my $i (split (/:/, $x{$id})) {
      my ($opt, $val)=split(/=/, $i);
      if (($opt eq "rarch") && ($val ne $u{arch})) { return 0 }
      if (($opt eq "rosrel") && ($val ne $u{osrel})) { return 0 }
      if (($opt eq "rplatform") && ($val ne $u{platform})) { return 0 }
      if (($opt eq "rpkg") && !$pkgs{$val}) { return 0 }
    }
    return 1;
  }

  if ($id eq "114045") {
    if ((exists $p{114049}) && ($p{114049}{irev} gt '03')) { return 0 }
  }
  if ($id eq "114790") {
    if (!$pkgs{"SUNWdcar"}  || $pkgs{"SUNWdcar"}  !~ "<1.1.0,REV=2002.05.29.15.02>") { return 0 }
    if (!$pkgs{"SUNWcrypr"} || $pkgs{"SUNWcrypr"} !~ "<1.1.0,REV=2002.05.29.15.00>") { return 0 }
  }
  if ($id eq "113332") {
    if (($pkgs{"SUNWhea"}) || ($pkgs{"SUNWmdb"})) { return 1 }
    if (($u{model} eq 'sun4u') || ($u{model} eq 'sun4us')) { return 1 }
    return 0;
  }
  if ($id =~ /115010|116478/) {
    if (($pkgs{"SUNWhea"}) || ($pkgs{"SUNWmdb"})) { return 1 }
    if ($u{model} eq 'sun4u') { return 1 }
    return 0;
  }
  if ($id =~ /109077|109078/) {
    if ((!$pkgs{"SUNWdhcm"}) && (!$pkgs{"SUNWdhcsu"})) { return 0 }
    if ($pkgs{"SUNWj3rt"}) { return 1 }
    return 0;
  }
  if ($id =~ /118739|116706/) {
    if (!$pkgs{"SUNWtsr"} || $pkgs{"SUNWtsr"} !~ "<2.5.0,REV=2003.04.03.21.27>") { return 0 }
  }
  if ($id =~ /118740|116707/) {
    if (!$pkgs{"SUNWtsr"} || $pkgs{"SUNWtsr"} !~ "<2.5.0,REV=2003.04.03.19.26>") { return 0 }
  }
  if ($id eq "118741") {
    if (!$pkgs{"SUNWtsr"} || $pkgs{"SUNWtsr"} !~ "<2.5.0,REV=2003.11.11.23.55>") { return 0 }
  }
  if ($id eq "118742") {
    if (!$pkgs{"SUNWtsr"} || $pkgs{"SUNWtsr"} !~ "<2.5.0,REV=2003.11.11.20.36>") { return 0 }
  }
  if ($id eq "110692") {
    if ((exists $p{108806}) && ($p{108806}{irev} ge '01')) { return 0 }
    if ((exists $p{108806}) && ($p{108806}{crev} ge '01')) { return 0 }
  }
  if ($id eq "111412") {
    if (!$pkgs{"SUNWmdi"} || $pkgs{"SUNWmdi"} !~ "<11.8.0,REV=2001.01.19.01.02>") { return 0 }
    if (!$pkgs{"SUNWsan"}) { return 0 }
  }
  if ($id eq "111097") {
    if (!$pkgs{"SUNWsan"}) { return 0 }
    if (!$pkgs{"SUNWqlc"}) { return 0 }
  }
  if ($id eq "111656") {
    if (!((exists $p{109460}) && ($p{109460}{irev} eq '05'))) { return 0 }
  }
  if ($id eq "112327") {
    if (($u{osrel} ne "5.6") && ($u{osrel} ne "5.7")) { return 0 }
  }
  if ($id =~ /109357/) {
    if ((exists $p{109778}) && ($p{109778}{irev} ge '08')) { return 0 }
    if ((exists $p{109778}) && ($p{109778}{crev} ge '08')) { return 0 }
  }
  if (($id eq "112125") && (($u{osrel} ne "5.6") || ($u{osrel} ne "5.7"))) { return 0 }
  if (($id eq "112126") && (($u{osrel} ne "5.8") || ($u{osrel} ne "5.9"))) { return 0 }
  if (($id eq "121430") && ($p{121430}{crev} ge '16') && (!$pkgs{"SUNWlucfg"})) { return 0 }
  if (($id eq "121431") && ($p{121431}{crev} ge '17') && (!$pkgs{"SUNWlucfg"})) { return 0 }
  if (($id eq "121428") && ($p{121428}{crev} ge '08')) {
    if (!((exists $p{121430}) && ($p{121430}{irev} ge '16'))) { return 0 }
  }
  if (($id eq "121429") && ($p{121429}{crev} ge '08')) {
    if (!((exists $p{121431}) && ($p{121431}{irev} ge '16'))) { return 0 }
  }
  if ($id =~ /120971|120972|120973|122803|122804|122805|126507|126508|126506/) {
    if (!($pkgs{"SUNWsamfsr"} || $pkgs{"SUNWsamfsu"})) { return 0 }
  }
  if ($id =~ /120974|120975|120976|122806|122807|122808|126511|126512|126510/) {
    if (!($pkgs{"SUNWqfsr"} || $pkgs{"SUNWqfsu"})) { return 0 }
  }
  if ($id =~ /116338|116339|118383|118384|125698|125699/) {
    if (!$pkgs{"SUNWxwplt"} || $pkgs{"SUNWxwplt"} !~ "<3.8.1800,REV=0.99.03.23>") { return 0 }
  }
  if (($id eq "119381") && ($u{osrel} ne "5.9") && ($u{osrel} ne "5.10")) { return 0 }
  if (($id eq "119775") && ($minor < 10)) { return 0 }
  if (($id eq "110938") && (($u{osrel} ne "5.8") || ($u{osrel} ne "5.9"))) { return 0 }
  if (($id eq "110973") && (($u{osrel} ne "5.8") || ($u{osrel} ne "5.9"))) { return 0 }

  if (($id eq "118605") && ($pkgs{"SUNWjaxp"})) { return 0 }
  if (($id eq "118607") && ($pkgs{"SUNWjmail"})) { return 0 }
  if (($id eq "118609") && ($pkgs{"SUNWjaf"})) { return 0 }
  if (($id eq "118611") && ($pkgs{"SUNWjato"})) { return 0 }
  if (($id eq "118613") && ($pkgs{"SUNWjcapi"})) { return 0 }
  if (($id eq "118615") && ($pkgs{"SUNWljdk"})) { return 0 }

  if (($id eq "143053") || ($id eq "146068") || ($id eq "147056")) {
    if ($pkgs{"SUNWefc"}) { return 1 }
    if (($pkgs{"SUNWiopc"}) && ($u{model} eq 'sun4v')) { return 1 }
    return 0;
  }

  if ($id =~ /146363|146364/) {
    if (!($pkgs{"SUNWsmbaS"} || $pkgs{"SUNWsmbar"} || $pkgs{"SUNWsmbau"})) { return 0 }
  }

  if ($id eq "112443") {
    if ((exists $p{108528}) && ($p{108528}{irev} ge '11')) { return 0 }
  }

  if ($id eq "112762") {
    if (!$pkgs{"SPROl90sx"} && !$pkgs{SPROl90s}) { return 0 }
  }

  if ($id =~ /147992|147993/) {
    if (!$pkgs{"SUNWgnome-im-client-root"}) { return 0 }
  }

  return 1;
}

sub get_uname {
  # Get information about host
  open(UNAME, $input{uname}) || errx ("Can't open $input{uname} ($!)");
  $_=<UNAME>;
  $_ || errx ("Empty uname output");
  chomp;
  close UNAME;

  ($u{osname}, $u{hostname}, $u{osrel}, $u{osversion}, $u{model}, $u{arch}, $u{platform})= split (/ /, $_);
  dbg ("osname from uname: $u{osname}");
  if ($u{osname} ne "SunOS") {
    $u{osrel}=$u{osversion}=$u{model}=$u{arch}=$u{platform}="?";
  }
  ($u{osname} && $u{hostname} && $u{osrel} && $u{osversion} && $u{model} && $u{arch} && $u{platform}) || errx ("Can't parse output from $input{uname}:\n  $_");
}

sub get_installed_packages {
  my $package;

  # Read pkginfo
  return unless (($u{osname} eq "SunOS") && ($u{osrel} ne "5.11"));
  open(PKGINFO, $input{pkginfo}) || errx ("Can't open $input{pkginfo} ($!)");
  if ($input{pkginfo} =~ /pkginfo-l.out/) {
    while(<PKGINFO>) {
      if (/\s+PKGINST:\s+(\S+)$/) { $package = $1; }
      if (/\s+ARCH:\s+(\S+)$/) { $pkga{$package} .= "<$1>"; }
      if (/\s+VERSION:\s+(\S+)$/) { $pkgs{$package} .= "<$1>"; }
    }
  } else {
    while(<PKGINFO>) {
      ($_ =~ /^(\S+) /) || errx ("Can't parse output from $input{pkginfo}:\n  $_");
      $package=$1;
      # Removing trailing .2/.3/... (multiple versions of same package)
      $package =~ s/\..*//;
      $_= <PKGINFO>;
      ($_ =~ /\((\S+)\) (.+)$/) || errx ("Can't parse output from $input{pkginfo}:\n  $_");
      $pkga{$package} .= "<$1>";
      $pkgs{$package} .= "<$2>";
    }
  }
  close(PKGINFO);
}

sub get_installed_patches {
  my $list='';
  my $done=0;
  my $nonsun=999999;

  return unless (($u{osname} eq "SunOS") && ($u{osrel} ne "5.11"));
  my $showrev_cmd=$showrev; ( -x $showrev_cmd) || ($showrev_cmd='');
  my $patchadd_cmd=$o{patchadd}; ( -x $patchadd_cmd) || ($patchadd_cmd='');

  # On Solaris <= 8, showrev doesn't support -R. Use patchadd instead.
  my ($major, $minor) = split (/\./, $u{osrel});
  if (($minor <= 8) && $o{root}) { $showrev_cmd='' }

  if ($o{fromfiles}) {
    dbg ("Reading from $input{showrev}");
    open(SHOWREV, $input{showrev}) || errx ("Can't open $input{showrev} ($!)");
    $/=""; $list= <SHOWREV>; $/="\n";
    close SHOWREV;
    $done=1;
  } else {
    foreach my $cmd ($showrev_cmd, $patchadd_cmd) {
      next unless $cmd;
      $input{showrev}="$cmd -p $o{root} 2>/dev/null";
      dbg ("Reading from $input{showrev}");
      $list=`$input{showrev}`;
      if (!$?) { $done=1; last } else { dbg ("Failed: $list") }
    }
  }
  $done || errx ("Couldn't get list of installed patches");

  $list || ($list= "No patches are installed\n");
  my @list= split(/\n/, $list);

  foreach my $i (sort @list) {
    # Oracle patches (123456-78, IDR123456-78)
    if (($i =~ /^Patch:\s+(\d{6})-(\d{2}).*/) || ($i =~ /^Patch:\s+IDR(\d{6})-(\d{2}).*/)) {
      my ($id, $rev)=($1,$2);
      init_patch($id);
      $p{$id}{irev}= $rev;
      if ($i =~ / Obsoletes: ([-0-9, ]*) /) {
        for my $j (split (/,* /, $1)) {
          my ($oid, $orev) = split (/-/, $j);
          ($id eq $oid) && next;
          init_patch($oid);
          $p{$oid}{iobsoletedby}="$id-$rev";
          #dbg ("$oid-$orev obsoleted by $id-$rev");
        }
      }
      if ($i =~ / Incompatibles: ([-0-9, ]*) /) {
        for my $j (split (/,* /, $1)) {
          my ($iid, $irev) = split (/-/, $j);
          init_patch($iid);
          #dbg ("$iid-$irev incompatible with $id-$rev");
        }
      }
      next;
    # Non-Oracle patches
    } elsif ($i =~ /^Patch:\s+(\S+)/) {
      my $id=$nonsun--;
      init_patch ($id); $p{$id}{irev}=$p{$id}{crev}="01"; $p{$id}{synopsis}=$1;
      next;
    }
    next if ($i =~ "No patches are installed");
    next if ($i =~ "No patches installed");
    next if ($i =~ /^$/);
    print ("WARNING: Can't parse output from $input{showrev}:\n  $i\n");
  }
}

sub get_current_xref {
  # Download most recent patchdiag.xref, if requested

  return if ($o{nocheckxref});

  lock_free($o{xrefdir}, "xref", 60) || errx ("Another instance of pca is downloading $input{xref} right now");

  # Remove possibly left-over size zero file
  if (-z $input{xref}) { unlink ($input{xref}) }

  # Check for existing and up to date local copy of xref file
  if ((-f $input{xref}) && (!$o{getxref})) {
    my $interval=10800; # 3 hours
    my ($mtime,$ctime)=(stat($input{xref}))[9,10];
    my $now=time();
    my $age=$now-$ctime;
    dbg ("xref mtime: " . localtime($mtime));
    dbg ("xref now  : " . localtime($now));
    dbg ("xref ctime: " . localtime($ctime));
    dbg ("xref age  : " . $age);
    if ($age < $interval) {
      dbg ("Local file $input{xref} is up to date");
      return;
    }
  }
  out ('info', "Downloading xref file to $input{xref}");

  # Check if we can write to xref directory
  if (! -w $o{xrefdir}) {
    my $msg="Can't write to xref download directory $o{xrefdir}";
    if ($o{getxref} || (! -f $input{xref})) {
      errx ($msg)
    } else { out ('info', $msg); return }
  }
  # Check if we can write to xref file
  if ((-f $input{xref}) && (! -w $input{xref})) {
    my $msg="Can't write to $input{xref}";
    if ($o{getxref}) {
      errx ($msg)
    } else { out ('info', $msg); return }
  }

  lock_create($o{xrefdir}, "xref", 1) || errx ("Another instance of pca is downloading $input{xref} right now");
  (-s $input{xref}) && rename ("$input{xref}", "$input{xref}.tmp");

  XREFURL: foreach my $xrefurl (split (/\s/, $o{xrefurl})) {
    if ($xrefurl =~ /^file:\/|^\//) {
      out ('info', "Trying $xrefurl");
      my $path=$xrefurl; $path =~ s/^file://;
      if (-r "$path/patchdiag.xref") {
        my ($atime, $mtime) = (stat("$path/patchdiag.xref"))[8,9];
        copy ("$path/patchdiag.xref", $input{xref});
        utime $atime, $mtime, $input{xref};
      }
      if (-s $input{xref}) { goto DONE }
      out ('info', "Failed");
      next XREFURL
    }
    if ($xrefurl =~ /^http:\/\/|^https:\/\/|^ftp:\/\//) {
      out ('info', "Trying $xrefurl");
      if (!$wget{path}) { out ('info', "Failed (can't find wget executable)"); next }
      if (download("xref", "", "url $xrefurl", $input{xref}, "")) { goto DONE }
      out ('info', "Failed ($wget{error})");
      next XREFURL
    }
    if ($xrefurl eq "oracle") {
      out ('info', "Trying Oracle");
      if (!$wget{path}) {
        out ('info', "Failed (can't find wget executable)");
        next XREFURL
      }
      my $try=1;
      while ($try <= $o{dltries} ) {
        out ('info', "Trying $wget{proto}://$o{ohost}/ ($try/$o{dltries})");
        if (download("xref", "", "oracle", $input{xref}, "")) { goto DONE }
        $try++; if ($try <= $o{dltries}) { sleep ($try*2) }
      }
      out ('info', "Failed ($wget{error})");
      next XREFURL
    }
    out ('info', "Trying $xrefurl");
    out ('info', "Failed (unknown type of URL)");
  }

FAIL:
  out ('info', "Failed (patchdiag.xref not found)");
DONE:
  # If we have a backup copy and the download failed, use the backup
  if (-s "$input{xref}.tmp" && ! -s $input{xref}) {
    rename ("$input{xref}.tmp", "$input{xref}")
  }
  # If we have a backup copy, check if the downloaded file is newer
  if (-s "$input{xref}.tmp") {
    my $odate; my $ndate; my $oage=-1; my $nage=-1;
    open (XREF, "<$input{xref}.tmp");
    while (<XREF>) {
      if ($_ =~ /PATCHDIAG TOOL CROSS-REFERENCE FILE AS OF (.*) /) {
        $oage= date2days ($odate=$1); dbg ("old xref age: $oage"); last;
      }
    }
    close XREF;
    open (XREF, "<$input{xref}");
    while (<XREF>) {
      if ($_ =~ /PATCHDIAG TOOL CROSS-REFERENCE FILE AS OF (.*) /) {
        $nage= date2days ($ndate=$1); dbg ("new xref age: $nage"); last;
      }
    }
    close XREF;
    if ((($oage == -1) && ($nage != -1)) || (($oage != -1) && ($nage != -1) && ($nage <= $oage))) {
      unlink ("$input{xref}.tmp")
    } else {
      out ('info', "Downloaded file ($ndate) older than local file ($odate)");
      rename ("$input{xref}.tmp", "$input{xref}")
    }
  }
  lock_remove($o{xrefdir}, "xref");

  if (-s $input{xref}) {
    if ($o{xrefown} || ($o{xrefdir} =~ /\/home\//)) {
      chmod 0644, $input{xref};
    } else {
      chmod 0666, $input{xref};
    }
    return;
  }
  (-z $input{xref}) && unlink ($input{xref});
}

sub get_current_patches {
  # Read patchdiag.xref
  # See http://sunsolve.sun.com/search/document.do?assetkey=1-9-240587-1
  #
  (-z $input{xref}) && errx ("Empty file $input{xref}");
  open(XREF, "<$input{xref}") || errx ("Can't open xref file $input{xref} ($!)");
  dbg ("patchdiag.xref size: " . (stat($input{xref}))[7]);
  while (<XREF>) {
    if ($_ =~ /PATCHDIAG TOOL CROSS-REFERENCE FILE AS OF (.*) /) {
      out ('info', "Using $input{xref} from $1"); last;
    }
  }
  undef $/; my $xref= <XREF>; $/="\n";
  close XREF;

  if (!$xref) { errx ("Corrupt file $input{xref}") }

  my @xref= split( /\n/, $xref );

  # Build our patch information table from the xref file.
  # patchdiag.xref is sorted, so if multiple revisions of a patch are listed,
  # the one with the highest revision comes last.
  #
  foreach my $i (sort @xref) {
    # Ignore comment lines, empty lines, possible HTML tags etc.
    next if ($i !~ /^\d{6}\|/);
    if ($i !~ /^\d{6}\|\d{2}\|.*\|.\|.\|.\|..\|.*\|.*\|.*\|.*$/) { errx ("Can't parse input from $input{xref}:\n  $i") }

    my ($id, $crev, $reldate, $rFlag, $sFlag, $oFlag, $byFlag, $os,
      $archs, $pkgs, $synopsis )= split( /\|/, $i);

    # Fix missing BAD mark
    ($id eq "114147") && ($byFlag=" B");

    init_patch($id);

    # If an installed patch revision is marked bad, note this.
    if (($p{$id}{irev} eq $crev) && ($byFlag =~ ".B")) {
      $p{$id}{ibad}= 1;
      dbg ("Bad patch installed: $id-$p{$id}{irev}");
    }

    # With --minimal, ignore obsolete state on recommended patches
    #
    if ($o{minimal} && ($rFlag eq 'R') && ($oFlag eq 'O')) {
      dbg ("$id-$crev: Resetting obsolete state");
      $oFlag=' ';
    }

    # If a patch revision is obsoleted or bad, use either the highest
    # non-obsoleted revision, or the highest obsoleted revision if all
    # revisions are obsoleted or bad.
    #
    if ($p{$id}{crev} ne "00") {
      if (($oFlag eq "O") || ($byFlag =~ ".B")) {
        if (!$p{$id}{obs} && !$p{$id}{bad}) { next; }
      }
    }

    # With --minimal, stick to the last revision marked as "Recommended"
    #
    if ($o{minimal} && $p{$id}{rec} && ($rFlag ne 'R')) {
      dbg ("$id-$crev: Sticking to recommended revision $p{$id}{crev}");
      $p{$id}{obs}=0;
      # A later revision of an RO patch might be obsoleted by another patch.
      # As we stop reading after RO, we have to check obsoletions of installed
      # patches here.
      if ($p{$id}{iobsoletedby}) {
        $p{$id}{obs}=1;
        $p{$id}{obsoletedby}=$p{$id}{iobsoletedby};
        dbg ("$id-$p{$id}{crev}: obsoleted by installed patch $p{$id}{iobsoletedby}");
      }
      next;
    }

    $p{$id}{crev}=$crev;
    if ($reldate ne '') { $p{$id}{reldate}=$reldate; }

    # Keep R flag status from a previous revision
    #if ($p{$id}{rec}) { dbg ("$id-$crev: Passing on R flag") }
    if ($rFlag  eq 'R' ) { $p{$id}{rec}=1; }

    $p{$id}{sec}=0; if ($sFlag  eq 'S' ) { $p{$id}{sec}=1; }
    $p{$id}{obs}=0; if ($oFlag  eq 'O' ) { $p{$id}{obs}=1; }
    $p{$id}{bad}=0; if ($byFlag =~ ".B") { $p{$id}{bad}=1; }
    $p{$id}{y2k}=0; if ($byFlag =~ "Y.") { $p{$id}{y2k}=1; }
    $p{$id}{os}=$os;
    $p{$id}{synopsis}=$synopsis;

    # If a patch is obsoleted by another patch, note it.
    # There are (at least) two forms, one with a patch revision
    # and one without. We check for both.
    #
    if ($p{$id}{obs}) {
      if ($synopsis =~ /Obsoleted by[ :]*(\d{6})-(\d{2})/) {
        if ($id ne $1) {
          $p{$id}{obsoletedby}="$1-$2";
          #dbg ("$id-$crev obsoleted by $p{$id}{obsoletedby}");
        }
      }
      if ($synopsis =~ /OBSOLETED by (\d{6})/) {
        if ($id ne $1) {
          $p{$id}{obsoletedby}="$1-01";
          #dbg ("$id-$crev obsoleted by $p{$id}{obsoletedby}");
        }
      }
    }

    # Patches might be obsoleted by installed patches, which are not
    # (yet) listed in patchdiag.xref.
    #
    if (($p{$id}{iobsoletedby}) && (!$p{$id}{obs})) {
      $p{$id}{obs}=1;
      $p{$id}{obsoletedby}=$p{$id}{iobsoletedby};
    }

    # Patch requires are coded into the archs field - separate them.
    $p{$id}{archs}='';
    $p{$id}{requires}='';
    # pkginfo removes spaces in the value of the ARCH field, so we do the
    # same for the arch column in the xref file.
    $archs =~ s/ //g;
    foreach my $r (split /\;/, $archs) {
      if ($r =~ /^\d{6}-\d{2}/) {
        $p{$id}{requires} .= "$r;";
        # We run init_patch here for required patches because they might
        # be missing in the xref file, and would be uninitialized later.
        my ($r_id, $r_rev)= split (/-/, $r);
        init_patch($r_id);
      } else {
        $p{$id}{archs} .= "$r;";
      }
    }
    # Patch incompatibilities are coded into the pkgs field
    $p{$id}{pkgs}='';
    foreach my $r (split /\;/, $pkgs) {
      if ($r =~ /^\d{6}-\d{2}/) {
        my ($r_id, $r_rev)= split (/-/, $r);
        init_patch($r_id);
        #dbg ("$r_id-$r_rev incompatible with $id-$crev");
      } else {
        $p{$id}{pkgs} .= "$r;";
      }
    }
  }
  # Pass on the R flag to obsoleting patches.
  return if ($o{minimal});
  my %rlist;
  foreach my $id (sort keys %p) {
    next unless ($p{$id}{rec} && $p{$id}{obs});
    my $tid=$id;
    while ($p{$tid}{obsoletedby} ne '') {
      my ($oby_id, $oby_rev)= split (/-/, $p{$tid}{obsoletedby});
      init_patch($oby_id);
      if (!$p{$oby_id}{rec}) { $rlist{$oby_id} .= "$tid " }
      $tid= $oby_id;
    }
  }
  foreach my $id (sort keys %rlist) {
    #dbg ("$id obsoletes $rlist{$id}: Passing on R flag");
    $p{$id}{rec}=1;
  }
}

sub init_patch {
  my $id=$_[0];

  # Every patch should be initialized only once.
  return if ($p{$id}{init});

  if($o{threads}) {
    $p{$id}=&share({});
    $p{$id}{output} = &share([]);
  }

  $p{$id}{irev}= $p{$id}{crev}= $p{$id}{prev}= '00';
  $p{$id}{synopsis}= 'NOT FOUND IN CROSS REFERENCE FILE!';
  $p{$id}{rec}= $p{$id}{sec}= $p{$id}{obs}= $p{$id}{bad}= $p{$id}{y2k}= 0;
  $p{$id}{recf}= $p{$id}{secf}= 0;
  $p{$id}{os}= '';
  $p{$id}{pkgs}= '';
  $p{$id}{stop}= '';
  $p{$id}{ignore}= '';
  $p{$id}{nobackup}= '';
  $p{$id}{reldate}= 'Jan/01/71';
  $p{$id}{age}= 0;
  $p{$id}{obsoletedby}= '';
  $p{$id}{iobsoletedby}= '';
  $p{$id}{archs}= '';
  $p{$id}{requires}= '';
  $p{$id}{listed}= 0;
  $p{$id}{ibad}= 0;
  $p{$id}{init}= 1;
  $p{$id}{dfori}= 0;
  $p{$id}{dloutput}= '';
  $p{$id}{dlfile}= '';
}

sub print_patch {
  my $id=$_[0];
  my ($char, $h_char, $irev, $crev, $rec, $sec, $bad, $age, $reldate, $os, $synopsis);

  if ($p{$id}{irev} lt $p{$id}{crev}) { $char='<'; $h_char='&lt;'; }
  if ($p{$id}{irev} eq $p{$id}{crev}) { $char='='; $h_char='='; }
  if ($p{$id}{irev} gt $p{$id}{crev}) { $char='>'; $h_char='&gt;'; }

  $irev= $p{$id}{irev}; if ($irev eq "00") { $irev= '--' };
  $crev= $p{$id}{crev}; if ($crev eq "00") { $crev= '--' };

  $rec='-'; if ($p{$id}{recf}) { $rec='r'; }; if ($p{$id}{rec}) { $rec='R'; }
  $sec='-'; if ($p{$id}{secf}) { $sec='s'; }; if ($p{$id}{sec}) { $sec='S'; }
  $bad='-';
  if (($p{$id}{irev} eq "00") && ($p{$id}{bad} )) { $bad='B' }
  if (($p{$id}{irev} ne "00") && ($p{$id}{ibad})) { $bad='B' }

  $os= $p{$id}{os}; $os =~ s/Trusted_Solaris/TS/;
  $synopsis= $p{$id}{synopsis};

  $age=calculateage($id);
  if ($age > 999) { $age=999; }
  $reldate=date2iso($p{$id}{reldate});

  if (!$o{listhtml}) {
    my $out=$o{format};
    $id=sprintf ("%6d", $id); $out =~ s/%p/$id/g;
    $out =~ s/%i/$irev/g; $out =~ s/%e/$char/g; $out =~ s/%c/$crev/g;
    $out =~ s/%r/$rec/g; $out =~ s/%s/$sec/g; $out =~ s/%b/$bad/g;
    $age=sprintf ("%3d", $age); $out =~ s/%a/$age/g;
    $out =~ s/%d/$reldate/g;
    $os=sprintf ("%-17s", $os); $out =~ s/%o/$os/g;
    $out =~ s/%y/$synopsis/g;
    my $n=sprintf ("%3d", $c{current}); $out =~ s/%n/$n/g;
    my $t=sprintf ("%3d", $c{total}); $out =~ s/%t/$t/g;
    print "$out\n";
  } else {
    # The patch download link will only work for patches in zip format,
    # there is no way to determine if it's in zip or tar.Z here.
    #
    $synopsis =~ s/\&/\&amp;/;
    printf "<tr>";
    my $url;
    $url="https://$o{ohost}/all_unsigned/$id-$crev.zip";
    foreach my $patchurl (split (/\s/, $o{patchurl})) {
      if ($patchurl =~ /pca-proxy\.cgi/) {
        if ($patchurl =~ /\.cgi$/) { $patchurl .= "?" }
        $url="${patchurl}$id-$crev.zip"; last
      }
    }
    printf "<td><a href=\"$url\">%6d</a>", $id;
    printf "<td>%2s<td>%1s<td>%2s<td>%1s%1s%1s<td align=right>%3s", $irev, $h_char, $crev, $rec, $sec, $bad, $age;
    $url="https://$o{ohost}/readme/README.$id-$crev";
    foreach my $patchurl (split (/\s/, $o{patchurl})) {
      if ($patchurl =~ /pca-proxy\.cgi/) {
        if ($patchurl =~ /\.cgi$/) { $patchurl .= "?" }
        $url="${patchurl}README.$id-$crev"; last
      }
    }
    printf "<td><a href=\"$url\">%s</a></tr>\n", $synopsis;
  }
}

sub print_header {
  if (!$o{listhtml} && !$o{noheader} && !$o{readme}) {
    print "Host: $u{hostname} ($u{osname} $u{osrel}/$u{osversion}/$u{arch}/$u{model})\n";
    if ($o{root}) { my $r=$o{root}; $r =~ s/-R //; print "Root: $r\n" }
    print "List: @slist" . ($o{minimal} ? "-minimal" : "") . " (" . int(@plist) . "/$agesum)\n\n";
    (@plist) || return;

    my $hdr= my $sep=$o{format};
    $hdr =~ s/%p/Patch /g; $hdr =~ s/%i/IR/g; $hdr =~ s/%e/ /g;
    $hdr =~ s/%c/CR/g; $hdr =~ s/%r/R/g; $hdr =~ s/%s/S/g;
    $hdr =~ s/%b/B/g; $hdr =~ s/%a/Age/g; $hdr =~ s/%y/Synopsis/g;
    $hdr =~ s/%d/Date      /g;
    $hdr =~ s/%n/Cnt/g; $hdr =~ s/%t/Tot/g;
    $hdr =~ s/%o/Operating System /; $sep =~ s/%o/-----------------/g;
    $sep =~ s/%p/------/g; $sep =~ s/%i/--/g; $sep =~ s/%e/-/g; $sep =~ s/%c/--/g;
    $sep =~ s/%r/-/g; $sep =~ s/%s/-/g; $sep =~ s/%b/-/g; $sep =~ s/%a/---/g;
    $sep =~ s/%d/----------/g;
    $sep =~ s/%n/---/g; $sep =~ s/%t/---/g;
    if ($sep =~ /%y/) {
      my $ysep = '-' x (78 - (length ($sep)-2)); $sep =~ s/%y/$ysep/g;
    }
    print "$hdr\n$sep\n";
  }
  if ($o{listhtml}) {
    print "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.01 Transitional//EN\"";
    print "\n  \"http://www.w3.org/TR/html4/loose.dtd\">\n";
    print "<html>\n<head>\n";
    print "<title>PCA report for $u{hostname}</title>\n";
    print "</head>\n<body>\n";
    print "$htmladditionalout\n";
    print "<h2>Host: $u{hostname} ($u{osname} $u{osrel}/$u{osversion}/$u{arch}/$u{model})<br>\n";
    if ($o{root}) { my $r=$o{root}; $r =~ s/-R //; print "Root: $r<br>\n" }
    print "List: @slist" . ($o{minimal} ? "-minimal" : "") . " (" . int(@plist) . "/$agesum)</h2>\n<table>\n";
    (@plist) || return;

    print "<tr><th>Patch</th>";
    print "<th><span title='Installed Revision'>IR</span></th><th></th>";
    print "<th><span title='Current Revision'>CR</span></th>";
    print "<th><span title='Recommended/Security/Bad Status'>RSB</span></th>";
    print "<th>Age</th>";
    print "<th>Synopsis</th></tr>\n";
  }
}

sub print_footer {
  if ($o{listhtml}) {
    print "</table>\n</body>\n</html>\n";
  }
}

sub get_readme {
  my $pp=$_[0];
  my ($id, $rev)= split (/-/, $pp);

  my $rfile= tempfile();
  $p{$id}{dlfile}=$rfile;
  out ('stderr', "Downloading README for $pp");

  # If patch is available in unzipped format, use its README
  if (-f "$o{patchdir}/$pp/README.$pp") {
    out ('stderr', "Trying $o{patchdir}/$pp");
    copy ("$o{patchdir}/$pp/README.$pp", $rfile);
    if (-s $rfile) { goto DONE } else { out ('stderr', "Failed") }
  }
  # If we have the zip/jar file, extract README from there. This doesn't work
  # for tar/tar.Z files, as Solaris tar cannot extract files to stdout.
  foreach my $ext ('zip', 'jar') {
    if ((-f "$o{patchdir}/$pp.$ext") && !$o{pforce}) {
      out ('stderr', "Trying $o{patchdir}/$pp.$ext");
      `$unzip -p $o{patchdir}/$pp.$ext $pp/README.$pp >$rfile 2>/dev/null`;
      if (!$? && (-s $rfile)) { goto DONE } else { out ('stderr', "Failed") }
    }
  }
  PATCHURL: foreach my $patchurl (split (/\s/, $o{patchurl})) {
    if ($patchurl =~ /^file:\/|^\//) {
      out ('stderr', "Trying $patchurl");
      my $path=$patchurl; $path =~ s/^file://;
      (-r "$path/README.$pp") && copy ("$path/README.$pp", $rfile);
      if (-s $rfile) { goto DONE }
      out ('stderr', "Failed");
      next PATCHURL
    }
    if ($patchurl =~ /^http:\/\/|^https:\/\/|^ftp:\/\//) {
      out ('stderr', "Trying $patchurl");
      if (!$wget{path}) { out ('info', "Failed (can't find wget executable)"); next PATCHURL }
      PROXY: if (download("readme", $pp, "url $patchurl", $rfile, "")) {
        goto DONE
      } else {
        out ('stderr', "Failed ($wget{error})");
        if (($wget{error} =~ /MOS data missing/) && checksoa()) { goto PROXY }
      }
      next PATCHURL
    }
    if ($patchurl eq "oracle") {
      out ('stderr', "Trying Oracle");
      if (!checksoa()) {
        out ('stderr', "Failed (no My Oracle Support Account data)");
        next PATCHURL
      }
      if (!$wget{path}) {
        out ('info', "Failed (can't find wget executable)");
        next PATCHURL
      }
      if ($wget{proto} ne "https") {
        out ('info', "Failed (wget doesn't support HTTPS)");
        next PATCHURL
      }
      my $try=1;
      while ($try <= $o{dltries}) {
        out ('stderr', "Trying https://$o{ohost}/ ($try/$o{dltries})");
        if (download("readme", $pp, "oracle", $rfile, "")) { goto DONE }
        $try++; if ($try <= $o{dltries}) { sleep ($try*2) }
      }
      out ('stderr', "Failed ($wget{error})");
      next PATCHURL
    }
    out ('info', "Trying $patchurl");
    out ('info', "Failed (unknown type of URL)");
  }
FAIL:
  out ('info', "Failed (README not found)");
DONE:
  $p{$id}{dlfile}="";

  if (-s $rfile) {
    out ('stderr', "Done");
    return ($rfile);
  }
  unlink ($rfile);
  return ();
}

sub update {
  if ($o{update} eq "never") {
    dbg ("Never update");
    return;
  }
  if (($o{update} ne "auto") && $o{proxy}) {
    dbg ("update option $o{update} not supported in proxy mode");
    return;
  }

  # If we can't write to pca, update won't work.
  if (($o{update} eq 'now') || ($o{update} eq 'auto')) {
    if (! -w $0) { errx ("Update option unavailable: Can't write to $0") }
  }

  if ($o{update} eq 'auto') {
    dbg ("Auto update");
    my $interval=86400; # One day
    my ($mtime,$ctime)=(stat($0))[9,10];
    my $now=time();
    my $age=$now-$ctime;
    dbg ("pca mtime : " . localtime($mtime));
    dbg ("pca now   : " . localtime($now));
    dbg ("pca ctime : " . localtime($ctime));
    dbg ("pca age   : " . $age);
    if ($age < $interval) {
      dbg ("age lower than interval");
      return;
    }
  }
  if (!$wget{path}) { errx ("Failed (can't find wget executable)") }

  my $udir= tempdir();
  my $ufile= "$udir/pca";
  dbg ("ufile: $ufile");

  # Copy pca to temporary directory, keeping the timestamps.
  my ($atime, $mtime) = (stat($0))[8,9];
  copy ($0, $ufile);
  utime $atime, $mtime, $ufile;

  my $ret;
  if ($o{pcaurl} =~ /^http.*pca-proxy\.cgi/) {
    $ret=download('pca', '', "url $o{pcaurl}", "$udir/pca", "");
  } else {
    $ret=download('pca', '', "url $o{pcaurl}", "", $udir);
  }
  $ret || errx ("Could not get pca from $o{pcaurl} ($wget{error})");

  my $newv;
  open (F, "<$ufile");
  while (<F>) {
    if ($_ =~ /^my \$version=\'(\d{8}-\d{2})\'/) {
      $newv=$1;
      dbg ("Old version: $version");
      dbg ("New version: $newv");
      last;
    }
  }
  close (F);

  my $updated=0;
  if ($newv eq $version) {
    if ($o{update} eq "auto") {
      utime $atime, $mtime, $0;
    } else {
      out ('info', "No new version available");
    }
  } else {
    out ('info', "New version available: $newv (current version: $version)");
    if (!$o{proxy}) {
      out ('info', "\nChanges:\n");
      open (F, "<$ufile");
      while (<F>) {
        if ($_ =~ /=head2 Version $newv/) {
          out ('info', "Version $newv");
          while (<F>) {
            if ($_ =~ /=head2 Version (\d{8}-\d{2})/) {
              ($1 le $version) && last;
            }
            $_ =~ s/=head2 //; chomp;
            out ('info', "$_");
          }
        }
      }
      close (F);
    }
    if ($o{update} ne "check") {
      out ('info', "Update");
      dbg ("Copy $ufile to $0");
      if (!copy ($ufile, $0)) {
        out ('info', "Failed ($!)");
      } else {
        my ($atime, $mtime)= (stat($ufile))[8,9];
        utime $atime, $mtime, $0;
        out ('info', "Done");
      }
      $updated=1;
    }
  }

  unlink ($ufile);
  rmdir ($udir);

  if (($o{update} eq "auto") && !$updated) { return }
  if ($o{proxy}) { return }
  exit $xval;
}

sub out {
  my $cat= shift;

  if ($o{proxy}) {
    if ($cat eq 'error') {
      my @args=@_;
      if ($args[0] !~ /^\d{3}/) { $args[0] = "500 $args[0]" }
      print "Content-type: text/plain\n";
      print "Status: @args\n\n";
      print "Internal Error: @args\n";
    }
    if ($o{debug}) {
      open (F, ">> $o{dbgfile}");
      my $now= localtime;
      print F $now, ": ", @_, "\n";
      close (F);
    }
    return;
  }
  if ($cat eq 'debug' ) { print STDERR @_, "\n"; return }
  if ($o{noheader}) { return }
  if ($cat eq 'stderr') { print STDERR @_, "\n"; return }
  if ($o{listhtml}) { $htmladditionalout .= "@_<br>" ; return }
  if ($cat eq 'info'  ) { print @_, "\n"; return }
  if ($cat eq 'error' ) { print STDERR "\nERROR: ",  @_, "\n"; return }
}

sub dbg {
  $o{debug} || return;

  my @args=@_;
  foreach my $i (@args) {
    $i =~ s/(Option user:) .*$/$1 <user>/;
    $i =~ s/(Option passwd:) .*$/$1 <passwd>/;
    $i =~ s/(header=X_PCA_USER:) .*$/$1 <user>/;
    $i =~ s/(header=X_PCA_PASSWD:) .*$/$1 <passwd>/;
    $i =~ s/(header=Authorization: Basic) .*$/$1 <base64-user-passwd>/;
  }
  out ('debug', @args);
}

sub date2iso {
  my $date=$_[0];
  my %months=(Jan=>"01", Feb=>"02", Mar=>"03", Apr=>"04", May=>"05", Jun=>"06", Jul=>"07", Aug=>"08", Sep=>"09", Oct=>"10", Nov=>"11", Dec=>"12");

  my ($m, $d, $y)= split (/\//, $date);
  $m=$months{$m};
  if ($y =~ /^[789]/) { $y = "19$y" } else { $y="20$y" }

  return ("$y-$m-$d");
}
  
sub calculateage {
  my $id=$_[0];

  if (!$p{$id}{age}) { $p{$id}{age}=date2days($p{$id}{reldate}) }
  return ($p{$id}{age});
}

sub date2days {
  my ($tmonth, $day, $year)=split(/\//, $_[0]);
  my %months=("Jan",0,"Feb",1,"Mar",2,"Apr",3,"May",4,"Jun",5,"Jul",6,"Aug",7,"Sep",8,"Oct",9,"Nov",10,"Dec",11);
  my $month=$months{$tmonth};

  return (int(($currenttime-timelocal(0,0,0,$day,$month,$year))/86400));
}

sub lock_create {
  my $lockd=$_[0]; my $tag=$_[1]; my $maxretry=$_[2];
  my $lockf="$lockd/.pcaLock.$tag";

  lock_free ($lockd, $tag, $maxretry) || return (0);

  unlink "$lockf";
  sysopen (LOCKF, $lockf, O_RDWR|O_CREAT|O_EXCL) || errx ("Can't write $lockf ($!)");
  print LOCKF "$$\n";
  close LOCKF;
  chmod 0666, $lockf;
  $locks{$tag}=$lockf;
  return (1);
}

sub lock_free {
  my $lockd=$_[0]; my $tag=$_[1]; my $maxretry=$_[2];
  my $lockf="$lockd/.pcaLock.$tag";

  my $retry=0;
  while ($retry < $maxretry) {
    if (-s "$lockf") {
      open (LOCKF, "<$lockf");
      chomp(my $pid = <LOCKF>);
      close LOCKF;
      if (kill (0, $pid) || ($! eq "Not owner")) {
        dbg ("Locking $lockf failed");
        $retry++;
        ($retry < $maxretry) && sleep (1);
        next;
      }
    }
    return (1);
  }
  return (0);
}

sub lock_remove {
  my $lockd=$_[0];
  my $tag=$_[1];

  unlink "$locks{$tag}";
  $locks{$tag}='';
}

sub tempdir {
  foreach my $i (1..10) {
    my $dir= "$o{tmpdir}/pca." . int(rand(1000000));
    next unless mkdir $dir, 0700;
    return $dir;
  }
  errx ("Couldn't create temporary directory in $o{tmpdir}");
}

sub tempfile {
  foreach my $i (1..10) {
    my $file= "$o{tmpdir}/pca." . int(rand(1000000));
    next if (-f $file);
    open (FILE, ">$file"); close (FILE); chmod 0600, $file; return $file;
  }
  errx ("Couldn't create temporary file in $o{tmpdir}");
}

sub log_msg {
  my $priority=$o{syslog};

  if ($priority eq "none") { return }
  if ($priority !~ /\./) { $priority .= ".notice" }
  system("$o{logger} -t pca -p $priority \"@_\"");
}

sub errx {
  out ('error', @_);
  cleanup();
  exit ($xval=1);
}

sub handler {
  errx ("Caught a SIG@_");
}

sub cleanup {
  dbg ("Cleanup");
  if ($dlfile) {
    dbg ("Removing $dlfile");
    unlink "$dlfile";
  }
  wgetrc_remove();
  if (($input{xref}) && (-s "$input{xref}.tmp")) {
    dbg ("Putting back copy of patchdiag.xref file");
    rename ("$input{xref}.tmp", "$input{xref}");
  }
  foreach my $id (keys %p) {
    if ($p{$id}{dlfile}) {
      dbg ("Removing $p{$id}{dlfile}");
      unlink "$p{$id}{dlfile}";
    }
  }
  if (@rlist) {
    dbg ("Removing @rlist");
    unlink (@rlist);
  }
  $patchxdir && rmtree ($patchxdir);
  foreach my $tag (keys %locks) {
    if ($locks{$tag}) {
      dbg ("Removing $locks{$tag}");
      unlink "$locks{$tag}";
    }
  }
  $sttyset && system "stty echo";
}

sub base64 {
  # From MIME-Base64-Perl-1.00

  my $res = pack("u", $_[0]);
  # Remove first character of each line, remove newlines
  $res =~ s/^.//mg; $res =~ s/\n//g;

  $res =~ tr|` -_|AA-Za-z0-9+/|;
  # fix padding at the end
  my $padding = (3 - length($_[0]) % 3) % 3;
  $res =~ s/.{$padding}$/'=' x $padding/e if $padding;
  return $res;
}

sub parse_args {
  # Get internal defaults
  foreach my $opt (@options) {
    my ($long, $short, $arg, $argtxt, $default, $help)=split (/\|/, $opt);
    if ($long eq 'cffile') {
      map { read_cffile($_) } split (/ /, $default);
    } elsif ($arg =~ /@/) {
      @{$o{$long}}=split (/ /, $default);
    } else {
      $o{$long}=$default;
    }
  }
  (basename($0) eq "pca-proxy.cgi") && ($o{proxy}=1);
  (basename($0) =~ "debug") && ($o{debug}=1);
  $o{proxy} && ($o{xrefdir} = getcwd());

  # Get defaults from optional configuration file(s)
  my @conf=();
  if ($o{proxy}) {
    push (@conf, dirname($0)."/../etc/pca-proxy.conf");
    push (@conf, "/etc/pca-proxy.conf");
    push (@conf, "./pca-proxy.conf");
  } else {
    push (@conf, dirname($0)."/pca.conf");
    push (@conf, dirname($0)."/../etc/pca.conf");
    push (@conf, "/etc/pca.conf");
    $ENV{HOME} && push (@conf, $ENV{HOME}."/.pca");
    push (@conf, "./pca.conf");
  }
  foreach my $i (@conf) { read_cffile ($i) }

  # Get defaults from optional environment variables (PCA_*)
  foreach my $opt (@options) {
    my ($long, $short, $arg, $argtxt, $default, $help)=split (/\|/, $opt);
    next if ($help eq "INTERNAL");
    my $env=uc("PCA_$long");
    next unless ($ENV{$env});
    if ($long eq 'cffile') {
      map { read_cffile($_) } split (/ /, $ENV{$env});
    } elsif ($arg =~ /@/) {
      push (@{$o{$long}}, split (/ /, $ENV{$env}))
    } else {
      $o{$long}=$ENV{$env}
    }
  }
  ($ENV{TMPDIR}) && (-d $ENV{TMPDIR}) && ($o{tmpdir}= $ENV{TMPDIR});

  # Set user/passwd if supplied via HTTP header to proxy
  ($ENV{HTTP_X_PCA_USER}) && (!$o{user}) && ($o{user}= $ENV{HTTP_X_PCA_USER});
  ($ENV{HTTP_X_PCA_PASSWD}) && (!$o{passwd}) && ($o{passwd}= $ENV{HTTP_X_PCA_PASSWD});

  # Proxy mode ?
  if ($o{proxy}) {
    if ($#ARGV != 0) { errx ("Missing argument") }
    if ($ARGV[0] =~ /:force/) { $ARGV[0] =~ s/:force//; $o{pforce}=1 }
    if ((($ARGV[0] !~ /^patchdiag.xref$/) &&
        ($ARGV[0] !~ /^\d{6}-\d{2}\.(zip|jar|tar|tar\.Z)$/) &&
        ($ARGV[0] !~ /^\d{6}-\d{2}$/) &&
        ($ARGV[0] !~ /^README\.\d{6}-\d{2}$/) &&
        ($ARGV[0] !~ /^pca$/))) {
      errx ("Illegal argument");
    }
    $o{proxy}=$ARGV[0];
  } else {
    # Get command line options
    my @olist=();
    foreach my $opt (@options) {
      my ($long, $short, $arg, $argtxt, $default, $help)=split (/\|/, $opt);
      next if (($help eq "INTERNAL") || ($help eq "ENVFILE"));
      $short && ($long="$long|$short");
      if ($arg) { $long .= "=$arg" } elsif ($Getopt::Long::VERSION >= 2.32) { $long .= "!" }
      push (@olist, $long);
    }
    Getopt::Long::config ("bundling", "no_ignore_case");
    $o{cffile}=sub { read_cffile ($_[1]) };
    GetOptions (\%o, @olist) || usage() && exit ($xval=2);
    delete $o{cffile};
  }
  if ($o{help}) { usage(); exit $xval }
  if ($o{man}) { man(); exit $xval }
  if ($o{version}) { version(); exit $xval }

  $o{listhtml} && ($o{list}=1);
  $o{pretend} && ($o{install}=1);
  $o{root} && ($o{root}="-R $o{root}");
  ($o{patchdir} !~ /^(\/|\w:\/)/) && ($o{patchdir}= getcwd()."/$o{patchdir}");
  ($o{xrefdir} !~ /^(\/|\w:\/)/) && ($o{xrefdir}= getcwd()."/$o{xrefdir}");
  $o{sshost} && ($o{ohost}=$o{sshost});

  # Set defaults
  $o{operands} && !@ARGV && (@ARGV=(split (/\s+/, $o{operands})));
  ($o{download} || $o{install} || $o{readme} || $o{getxref} || $o{proxy}) || ($o{list}=1);

  # Show all options and configuration files in debug output
  foreach my $opt (@options) {
    my ($long, $short, $arg, $argtxt, $default, $help)=split (/\|/, $opt);
    if ($long eq 'cffile') {
    } elsif ($arg =~ /@/) {
      next unless (@{$o{$long}});
      dbg ("Option $long: @{$o{$long}}");
    } else {
      next if ($o{$long} eq $default);
      dbg ("Option $long: $o{$long}")
    }
  }
  dbg ("Command: $0");
  dbg ("ARGV: @ARGV");
  dbg ("Version: $version");
  dbg ("CWD: " . getcwd());
  ($conf_dbg) && dbg ("Config files: $conf_dbg");
  ($o{debug} && !$o{proxy}) && log_msg ("Running pca $version in debug mode");

  if ($o{update} !~ /^(never|check|now|auto)$/) {
    errx ("Invalid TYPE specified with --update: $o{update}");
  }
}

sub process_patch_exceptions {
  foreach my $i ('stop', 'ignore', 'nobackup') {
    foreach my $j (@{$o{$i}}) {
      #dbg ("$i: $j");
      if (($i eq 'nobackup') && ($j =~ /^all$/)) { $o{$i}='all'; last }
      if ($j =~ /^(\d{6})$/) { init_patch($1); ($p{$1}{$i}= "00"); next }
      if ($j =~ /^(\d{6})-(\d{2})$/) { init_patch($1); ($p{$1}{$i}= $2); next }
      errx ("Invalid patch ID with --$i: $j") unless ($i eq 'ignore');
    }
  }
}

sub process_patch_flags {
  foreach my $i ('rec', 'sec') {
    foreach my $j (@{$o{$i}}) {
      #dbg ("$i: $j");
      if ($j =~ /^(\d{6})(-\d{2})*$/) { init_patch($1); ($p{$1}{"${i}f"}= 1); next }
      errx ("Invalid patch ID with --$i: $j")
    }
  }
}

sub read_cffile {
  return unless -f $_[0];
  my $id=join (":", (stat($_[0]))[0..1]); # st_dev and st_ino
  if ($conf_read{$id}) { return } else { $conf_read{$id}=1 }

  local *CONF;
  open (CONF, "<$_[0]") || return;
  $conf_dbg .= "$_[0] "; dbg ("Reading cffile $_[0]");
  while (<CONF>) {
    chomp;
    s/^#.*$//; s/\s+#.*$//; s/^\s*//; s/\s*$//;
    next if /^$/;

    # Deprecated
    if (/(\d{6})\s+ignore/) { push (@{$o{ignore}}, $1); next }
    if (/(\d{6}-\d{2})\s+ignore/) { push (@{$o{ignore}}, $1); next }
    if (/(\d{6})\s+\+rec/) { push (@{$o{rec}}, $1); next }
    if (/(\d{6})\s+\+sec/) { push (@{$o{sec}}, $1); next }

    next unless (/(\w+)\s*=\s*(.+)/); my ($name, $value)=($1,$2);
    foreach my $opt (@options) {
      my ($long, $short, $arg, $argtxt, $default, $help)=split (/\|/, $opt);
      next if ($help eq "INTERNAL");
      next unless ($name eq $long);
      if ($long eq 'cffile') {
        map { read_cffile($_) } $value;
      } elsif ($arg =~ /@/) {
        push (@{$o{$long}}, $value)
      } else {
        $o{$long}=$value
      }
      last
    }
  }
}

sub usage {
  print<<EOT
Usage: $0 [OPTION] .. [OPERAND] ..

Operands:
  patch group:    missing, installed, all, total, unbundled, bad
                  Add r, s or rs at the end to list Recommended,
                  Security or Recommended/Security patches only.
  patch ID:       123456, 123456-78
  patch file:     123456-78.zip, 123456-78.jar, 123456-78.tar.Z
  file name:      patchlist.txt

Options:

EOT
;

  foreach my $opt (@options) {
    my ($long, $short, $arg, $argtxt, $default, $help)=split (/\|/, $opt);
    next if (($help eq "INTERNAL") || ($help eq "ENVFILE") || ($help eq "DEPRECATED"));
    $short && ($short="-$short,");
    $argtxt && ($long="$long=$argtxt");
    printf "  %3s --%-15s%s\n", $short, $long, $help;
  }
  return 1;
}

sub man {
  eval "use Pod::Usage";
  if ($@) { errx ('Required module Pod::Usage not found') }

  # Change uid to something secure as pod2usage does not run as root.
  # This snippet is taken from perldoc. See the comments there.
  my $id= eval { getpwnam("nobody") };
  $id= eval { getpwnam("nouser") } unless defined $id;
  $id= -2 unless defined $id;
  eval {
    $< = $id; # real uid
    $> = $id; # effective uid
    $< = $id; # real uid
    $> = $id; # effective uid
  };
  pod2usage( -exitstatus => 0, -verbose => 2 );
}

sub version {
  print "pca $version\n";
}

__END__

=head1 NAME

PCA - analyze, download and install patches for Oracle Solaris

=head1 SYNOPSIS

pca [OPTION] .. [OPERAND] ..

=head1 DESCRIPTION

PCA is a perl script which generates lists of installed and missing
patches for Oracle Solaris systems and optionally downloads and installs
patches. By default, if run without any option or operand, PCA
shows a list of all patches which are not installed in their most recent
revision.

The output of the pkginfo, showrev and uname commands is used to gather
information about the system. Oracle offers a patch cross-reference file
called patchdiag.xref which contains information about all available patches.
This file is downloaded by PCA automatically to /var/tmp/ and kept up-to-date.
If the file
exists and is not writable, PCA uses it and won't try to update it.

=head1 SAMPLE OUTPUT

Here's some sample output from I<pca -l all>, which shows a list
of all installed and missing patches:

  Using /var/tmp/patchdiag.xref from Feb/29/04
  Host: myhost (SunOS 5.9/Generic_117171-09/sparc/sun4u)
  List: all (7/2182)

  Patch  IR   CR RSB Age Synopsis
  ------ -- - -- --- --- --------------------------------------------------
  112785 42 < 43 RS-  18 X11 6.6.1: Xsun patch
  112787 01 = 01 --- 999 X11 6.6.1: twm patch
  112807 10 = 10 RS-   9 CDE 1.5: dtlogin patch
  113039 -- < 06 ---  76 SAN 4.4.1: Sun StorEdge Traffic Manager patch
  113040 -- < 08 R--  77 SAN 4.4.1: fctl/fp/fcp driver patch
  113477 02 > -- --- 999 NOT FOUND IN CROSS REFERENCE FILE!
  117114 -- < 02 ---   4 CDE 1.5: sdtwebclient patch

The header includes some general information about the patchdiag.xref
file, the host (I<Host:>) and the listed patches (I<List:>). The numbers
in parantheses are the number of listed patches and the sum of their ages
in days; when listing missing patches, this is a rough indicator of the
current patch state.

The first column (I<Patch>) contains the patch number, followed by the
installed revision (I<IR>) and the current revision
(I<CR>), with one of E<lt>, E<gt>, or = between
them, which tells whether the installed patch revision is lower, equal or
higher than the current revision of the patch. The I<RSB> column lists
the Recommended/Security/Bad flag of the patch. I<Age> shows the
number of days since the patch was released, and
I<Synopsis> shows a short description of the patch.

On this system, revision 42 of patch 112785 is installed, but a newer
revision (43) is available. This patch is marked Recommended/Security.
Patch 112787 is installed in revision 01, which is the most
recent revision of the patch.
112807 is marked Recommended/Security, and it's up-to-date.

Patches 113039, 113040 and 117114 are not installed
at all, and 113040 is marked Recommended.

113477 is installed, but not listed in the cross-reference file.
New Solaris update releases often have patches pre-installed which
are not yet listed in patchdiag.xref.

Often one patch requires other patches to be installed before
it can be installed. PCA resolves these dependencies,
and lists patches in their correct order. This can be seen
in the patch list when a greater patch number is shown
before a lower one, or when a patch which is not marked R/S is shown
on the list of missing R/S patches.

=head1 OPTIONS

=over

=item -l, --list

List patches. See OPERANDS on how to specify which patches
are listed.

=item -L, --listhtml

Like I<-l>, but generates output in HTML format, including
links to patch READMEs and downloads. If I<patchurl> is set and
points at a local patch proxy, the links in HTML output will point there,
too.

=item -d, --download

Download patches. See OPERANDS on how to specify which patches
are downloaded. Patches are placed in the current directory or
in I<patchdir>, if set. A My Oracle Support Account and a wget binary
with SSL/HTTPS support are required.

=item -i, --install

Download and install patches. See OPERANDS on how to specify
which patches are installed. Requires PCA to be run as root. Downloaded
patches are removed after successful installation, unless I<--download>
is used, too.

=item -I, --pretend

Like I<-i>, but only pretend to install patches. Can be used
to find out if any of the patches require a reboot.

=item -r, --readme

Display patch READMEs. See OPERANDS on how to specify
which READMEs are displayed.
The patch README is
extracted from a previously downloaded patch file or downloaded
directly from Oracle, which requires a My Oracle Support Account and a
wget binary with SSL/HTTPS support.

=item -u, --unzip

Download and unzip patches. See OPERANDS on how to specify
which patches are unzipped. Unzipped patch directories are placed
in the current directory or in I<patchdir>, if set. Downloaded
patches are removed after successful unzip operation, unless I<--download>
is used, too. It is not necessary to unzip patches with this option
before installing them. Instead, this can be used to peek into the
contents of a patch zip file.

=item -x, --getxref

Download most recent patch cross-reference file.
If the file does not exist or is older than 3 hours, PCA tries to
download it on its own before anything else.

=item -X, --xrefdir=DIR

Set location of the cross-reference file. The default is
I</var/tmp> (in proxy mode, the default is the current directory).
By default, patchdiag.xref is writable for all users. If the I<xrefown>
option is set, or the I<xrefdir> option contains I</home>,
the cross reference file will be
writable by the current user only.

=item -y, --nocheckxref

Do not check for updated patch cross-reference file. Use this option
to maintain a global baseline patch set.

=item --xrefown

If set, patchdiag.xref will be writable for the current
user only.

=item --nocache

If a proxy is used to access the Internet, this option advises
it to not cache patchdiag.xref. Useful if the proxy can't be trusted
to always return an up-to-date version of the file.

=item -P, --patchdir=DIR

Set directory to which patches are downloaded. The default is
the current working directory.

=item -a, --askauth

Deprecated.

=item --user=USER

Login name for My Oracle Support Account authentication.

=item --passwd=PASS

Password for My Oracle Support Account authentication.

=item --supplevel

Deprecated. Oracle broke the interface to query this information.

=item --patchurl=URL

PCA will download patches and READMEs from this URL. Multiple URLs
separated by whitespace can be specified. Any URL starting with
file:/, ftp://, http:// or https://, and absolute paths can be
used. The default is the special keyword I<oracle>, meaning the
Oracle patch server. See LOCAL PATCH SERVER for more information.

=item --xrefurl=URL

PCA will download patchdiag.xref from this URL. Multiple URLs
separated by whitespace can be specified. Any URL starting with
file:/, ftp://, http:// or https://, and absolute paths can be
used. The default is the special keyword I<oracle>, meaning the
Oracle patch server. See LOCAL PATCH SERVER for more information.

=item --stop=ID

Stop after patch ID. When the specified patch ID is reached during
listing, downloading or installing patches all operations are stopped.
The option will be ignored if the same patch ID is explicitly included
in the OPERANDS.

=item --ignore=WHAT

Ignore certain patches. The patch will not be listed, downloaded
or installed. Specify a patch ID
without revision (I<123456>) to ignore any revision of patch 123456.
Specify I<123456-78> to ignore only revision 78 of patch 123456; newer
revisions will not be ignored. Specify a search pattern like I<JavaSE>
to ignore patches whose synopsis matches the pattern.
If an ignored patch is required by another patch, this patch might
fail to install due to the missing patch dependency.

=item --rec=ID

Set Recommended flag on patch ID. Useful to add single patches
to the set of recommended patches. The patch will be marked with a lowercase
I<r> in PCA's output.

=item --sec=ID

Set Security flag on patch ID. Useful to add single patches
to the set of security patches. The patch will be marked with a lowercase
I<s> in PCA's output.

=item -p, --pattern=REGEX

List only patches whose synopsis matches the search pattern
REGEX. This can be a simple string like I<mail> or a regular
expression like I<[kK]ernel>. If the pattern starts with a
I<!>, only patches which do not match the pattern are shown.

=item -n, --noreboot

Install only patches that don't require a reboot after
installation.

=item --minage=DAYS

List only patches which are at least DAYS old.

=item --maxage=DAYS

List only patches which are at most DAYS old.

=item --nodep

Do not resolve patch dependencies.

=item --minimal

Use minimal (instead of latest) revision for recommended patches.
In combination with the I<missingr> patch group this can be used
to check a system against the same set of patches as included in
the I<Recommended Patchset for Solaris>, containing the minimal
revisions of all critical patches recommended to be installed
proactively. In short, "pca --minimal --install missingr" should
give the same result as installing the I<Recommended Patchset for
Solaris>. Use of I<--minimal> with any other patch group than
I<missingr> might give unexpected results.

=item --syslog=TYPE

Syslog priority to log patch installs to. The default is
I<daemon.notice> which gets logged to I</var/adm/messages>. Specify
facility and severity (e.g. I<local7.info>) or a facility only
(e.g. I<local7>, the default severity is I<notice>). Use I<none> to
disable logging to syslog.

=item -k, --nobackup=ID

Do not back up files to be patched for patch ID. This works by running
patchadd with its I<-d> option. Patches can not be backed out if this
option is used. Specify a patch ID with or without a revision or the
special ID I<all> to not back up files for any patch.

=item -B, --backdir=DIR

Saves patch backout data to DIR. This works by running patchadd
with its I<-B> option.

=item -s, --safe

Safe patch installation. Checks all files for local modifications
before installing a patch. A patch will not be installed if files with
local modifications would be overwritten.

=item -G, --currentzone

Make patchadd modify packages in the current zone only. This
works by running patchadd with its I<-G> option. This option works
on Solaris 10 or newer only.

=item --patchadd=FILE

Path to an alternative patchadd command.

=item -H, --noheader

Don't display descriptive headers and other information, just one line
per patch. Useful if re-using PCA's output in own scripts.

=item --format=FORMAT

Set output format to FORMAT. The default format is
I<%p %i %e %c %r%s%b %a %y>. Use I<%p> for the patch number,
I<%i> for the installed revision, I<%e> for information whether
the installed revision is lower, equal or higher than the current revision
(I<%c>). Use I<%r>, I<%s> and I<%b> for the Recommended,
Security and Bad flag, I<%a> for the age, I<%d> for the release date,
I<%o> for OS and I<%y> for the Synopsis. Use I<%n> as a patch counter
and I<%t> for the total number of patches.
Example: With the format string I<%p-%c %y> PCA shows patches
in the same format as smpatch. Use of this option in combination with
I<--listhtml> is unsupported.

=item -f, --fromfiles=DIR

Read uname/showrev/pkginfo output from files in the specified
directory, where DIR can also be a file name prefix. See
CREATING PATCH REPORTS FOR REMOTE MACHINES for details.

=item --dltries=NUM

Try downloads from Oracle's download server NUM times. The
default is 1. Can be raised to reduce failed patch downloads when
Oracle's patch download server is unresponsive.

=item -F, --force

Force local caching proxy to download patchdiag.xref, patches
and patch READMEs from Oracle's download server, even if the file is already
in the cache. Useful to download updated patch READMEs for bad
patches.

=item -R, --root=DIR

Set alternative root directory. This can be useful for Live Upgrade,
to analyze patches in an alternate root environment or to point PCA at
the mini-root of a jumpstart install server.

=item --wget=PATH

Path to the wget command. Specify the name of the wget binary or the
directory containing the wget binary. When multiple wget binaries are
found, the newest with the best protocol support is used.

=item --wgetproxy=URL

Default proxy for wget.

=item --wgetopt=OPT

Feed option OPT directly to wget as-is. Usually only needed for debug
reasons and to work around local configuration issues. Leading
I<-/--> must be included and OPT must be quoted!

=item --logger=FILE

Path to (alternative) logger command.

=item -t, --threads=NUM

Number of concurrent download threads.  See THREADS for details.

=item --update=TYPE

Check for available updates for PCA itself. TYPE can be I<never>, I<check>,
I<now> or I<auto>. See UPDATE PCA for more information.

=item --pcaurl=URL

Set the URL which is used by I<update> to check for new versions of PCA.
See UPDATE PCA for more information.

=item --ssprot=PROT

Deprecated.

=item --sshost=HOST

Deprecated.

=item --ohost=HOST

Use HOST as the hostname or IP address of the Oracle download server.
The default is I<getupdates.oracle.com>.

=item --norootchk

When using the I<safe> or the I<install> option, root permission is
required to run pkgchk or patchadd. Use this option to skip
the check, e.g. when using sudo or RBAC.

=item --cffile=FILE

Read FILE as additional configuration file. Use I<cffile=FILE> in a
configuration file to include FILE.

=item -V, --debug

Show debug output on stderr. This includes output generated by patchadd. When
running in proxy mode, debug output will be written to the file
/var/tmp/pca-proxy-debug.txt.

=item -h, --help

Print help on command line options.

=item -m, --man

Print manual page. This requires the Pod::Usage module.

=item -v, --version

Print version information.

=back

If no option is specified, the I<-l> option to list patches is used.

=head1 OPERANDS

The operands determine which patches are listed (I<-l>),
downloaded (I<-d>), installed (I<-i>) or whose READMEs
are displayed (I<-r>). Multiple operands
can be specified. Supported operands
are I<patch group> (missing, installed, all, total, unbundled, bad),
I<patch ID> with or without revision
(123456-78 or 123456), I<patch file> (123456-78.zip) and
I<file name> (patchlist.txt).

The patch groups can be used to specify all missing patches (I<missing>),
all installed patches (I<installed>), both installed and missing patches
(I<all>), all patches listed in patchdiag.xref (I<total>),
patches not associated with a software package (I<unbundled>)
or installed patches which are marked Bad (I<bad>).
By adding I<r>, I<s> or I<rs> to any of
the patch groups, only patches from the patch group which are marked
Recommended, Security or either Recommended or Security are specified.
Examples are I<missings> for all missing Security patches, or
I<allrs> for all Recommended/Security patches.
Patch groups can be shortened by using the first letter of the patch
group plus optional r/s/rs
(e.g. I<ms> for missings or I<ars> for allrs).

Patch IDs like I<123456-78> or I<123456> are used to specify
single patches. If no revision (I<-78>) is specified, patch dependencies
will be resolved. If the name of a patch file like
I<123456-78.zip> is specified, it has the same effect as using
I<123456-78>. This can be useful to install a list of already
downloaded patches with I<pca -i *.zip>.

If a I<file name> is specified, the file is read and its
contents are added to the list of operands line-by-line. A file
can contain other file names. If the file name is equal to a valid
patch group name it will not be read.

The patch list can be limited to patches whose synopsis line contains
a search pattern by using any patch group in combination with the
I<--pattern=REGEX> option.
A command like I<pca -p mail> shows any missing patch containing
the I<mail> keyword in its description.
If the search pattern contains whitespace or special characters, enclose
it in quotation marks:
I<pca -p Studio -l total> shows patches for all versions of
Sun Studio. If the pattern starts with I<!>, the patch list is
limited to patches which do not match the pattern.

If no operands are specified, the I<missing> operand is used.

=head1 CONFIGURATION

The behaviour of PCA can be configured by setting any option either
in a configuration file, as an environment variable with the I<PCA_>
prefix or on the command line. See OPTIONS for a complete list; only
the long names can be used in configuration files and for environment
variables.

At first, the configuration files are read. PCA reads I<pca.conf>
in the directory where PCA is installed, I<../etc/pca.conf> of the
directory where it is installed, I</etc/pca.conf>, I<$HOME/.pca>
and I<pca.conf> in the current
directory, in this order. In proxy mode the files I<../etc/pca-proxy.conf>,
I</etc/pca-proxy.conf> and
I<pca-proxy.conf> in the current directory are read instead.
Options are set by specifying
I<option=value> in the file. Example: To set the path of the wget command,
use I<wget=/opt/bin/wget>. To enable debug output, use
I<debug=1>.

Then, all environment variables matching I<PCA_OPTION> are
read. Example:
To set the patch download directory, set I<PCA_PATCHDIR> to
I</some/dir/>. To set the I<noheader> option, set I<PCA_NOHEADER>
to I<1>.

At last, the command line options are read. Example: To set the location
of the patch xref file, use I<-X /tmp> or I<--xrefdir=/tmp>.
To set the option for safe patch installation, use I<-s> or I<--safe>.

All boolean options (i.e. those which do not take an argument) can
be negated on the command line by specifying I<--no-option> to override
settings from configuration files. Version 2.32 or newer of the
Getopt::Long module is required. Example: If I<noreboot=1> is set in
I<pca.conf> it can be overridden with I<--no-noreboot>.

The I<operands> option can only be used in configuration files and as
an environment variable. It sets the default OPERANDS.

In a configuration file, everything after a I<#> character is
regarded as a comment and ignored.

=head1 PATCH DOWNLOAD AND INSTALLATION

The I<-d> option downloads patches to the current directory, I<-i>
downloads and installs them.
The download option can be used as a regular user. The external command
wget is used for the actual download. If it can't be found in the
default paths, set the I<wget> option to contain the path to the
wget command.
The install option
requires PCA to be run as root. It uses I<patchadd> to
install the patches.
Using I<-I> instead of I<-i>
pretends to install patches, but does not actually install any patch.

After the installation of each patch, a status line shows the
current time, the time used to install the patch and the total
run time. It also includes the current/total number of patches
and counts for successful, skipped and failed patch installs.

The patches are downloaded from Oracle's patch download server.
To download patches from Oracle, a My Oracle Support (MOS) Account
is required. For most patches a Support Contract is required, too
(see SUPPORT LEVELS for more information).
Set the two options I<user> and I<passwd> to contain
the MOS user name and password. If unset, PCA asks for
MOS Account data interactively. If I<user> is set, but
I<passwd> is not, PCA will ask for the password.

As PCA analyzes the information in the cross-reference file to resolve
patch dependencies, it lists and installs patches in the correct order.
Patches for the patch installation utilities will always be installed
first to avoid issues with subsequent patches.

For some patches, a (reconfiguration) reboot is
recommended or required after installation. The /reconfigure file
is created as needed and a message is shown in the summary.
When the I<install> or I<pretend> option
is combined with the I<noreboot> option, only patches which do
not require a reboot are installed. This information is contained
in the patch distribution file. Therefore, even if I<noreboot>
is specified, the patches are downloaded anyway; only the installation
is skipped.

I<patchadd> normally keeps a backup of all files it modifies.
Using the I<--nobackup=ID> option with PCA instructs
I<patchadd>
to not keep backup copies of replaced files (see the I<-d> option in
patchadd's man page).

Sometimes a patch re-delivers
and silently overwrites files which have been modified locally. PCA
tries to overcome this issue with its safe patch installation mode.
Before installing a patch, PCA checks all files listed in the patch
README for local modifications. If any modified file is in danger
of being overwritten, a warning is shown and the patch is skipped.
Safe mode is off by default, and can be turned on by using I<-s> or
I<--safe> in
combination with I<-i> (install patches) or I<-I> (pretend to install
patches). You must be root to use I<-s>. Running I<pca -s -I> is a
safe way of identifying problematic patches without actually installing them.

In rare cases, patches modify or replace files without updating the
checksum in the package database used by PCA. Installing a more recent
revision of the same patch will fail although no local modifications
have been made to a file. Patch installation can be forced by not
using the I<safe> option.

Running I<pca -si missingrs> on a regular basis
is enough to keep the system at the recommended patch level.
This is quite comfortable and works without problems in many cases.
As some patches require special handling,
it's recommended to read the README of every patch before
installation. PCA's I<-L> option for HTML output and the
I<--readme> option to display patch READMEs are handy for that.

Sometimes installing a patch might fail because of inconsistencies
in the patchdiag.xref file, the patch README and the
information contained inside the patch. Often this gets fixed in a new
version of patchdiag.xref or in a new revision of the patch.
Either try again a few days later or take a look at the
I<Notes> section on the PCA web site, where some problematic
patches are listed.

=head1 SUPPORT LEVELS

In order for a user to download a patch, the user must have a
Support Level on their My Oracle Support (MOS) Account that matches
the Support Level on the patch. A certain type of Support Contract
includes one or more Support Levels.

To find out which Support Levels a User and a Patch have, follow
the instructions in Knowledge Article ID I<1269292.1> on MOS.

Possible Support Levels and Support Contract Coverage:

=over

=item OS (Operating System)

Solaris patches and updates.
Requires I<Premier Support for Operating Systems> or
I<Premier Support for Systems>.

=item PUB (Public Patches)

Oracle Open Office/StarOffice and patch utilities.
No Support Contract required.

=item SW (Software)

Existing Oracle software and Sun middleware.
Requires I<Premier Support for Software>.

=item FMW (Firmware)

Firmware, drivers, bios, system controller software, ALOM/ILOM, diagnostics.
Requires I<Hardware Warranty> or I<Premier Support for Systems>.

=item VIN (Vintage Solaris)

Solaris 8.
Requires I<Oracle Solaris Extended Support>.

=item EXS (Extended Support)

EOL Oracle Software.
Requires I<Lifetime Support>.

=back

=head1 LOCAL PATCH SERVER

On a local network, it might be useful to have a local patch
server.
There are two ways to set up a local patch server for PCA, using the
I<patchurl> and I<xrefurl> options.
With these options, alternative locations for patches, patch READMEs
or patchdiag.xref can be specified. Multiple URLs and the special
keyword I<oracle> can be used to make PCA check various local or
remote resources and Oracle's server. Like this, you can create
patch repositories with already downloaded patches and let PCA
always look there before trying to access the Oracle server.

Create the local patch repository by copying downloaded patch files
(e.g. 123456-78.zip), patch READMEs (e.g. README.123456-78) and/or
patchdiag.xref to a
directory which is available via NFS or on a local web server.
Point PCA at it by setting the I<patchurl> and/or I<xrefurl>
options to the URL
(e.g. "file:/pca/ oracle" or "http://www.my.org/patches/").

The more advanced method uses PCA to work as a local caching proxy for itself.
Create a directory in the document root of the local web server, and
link or copy pca there under the name I<pca-proxy.cgi>. Make sure that
the directory (or the directories specified with the I<xrefdir> and I<patchdir>
options) are owned and writable by the user under which CGI scripts run,
as patches, patch READMEs and patchdiag.xref will be stored there.
Verify that the
web server is configured to run CGI scripts (for apache, check the ExecCGI
and AddHandler options in httpd.conf).
Create a pca.conf
file in the same directory to specify My Oracle Support Account data. On the client,
point
PCA at the caching proxy by setting the I<patchurl> and I<xrefurl>
options to e.g.
http://www.my.org/patches/pca-proxy.cgi.

In proxy mode, if a patch or
patch README exists in the local cache directory, it is delivered
immediately. If it doesn't, the file is downloaded from Oracle's
patch server, put into the cache, and delivered. For patchdiag.xref,
I<pca-proxy.cgi> will always make sure that it has a recent
version of this file and deliver it from its cache.

With a local caching proxy in place, client systems running PCA and
using this proxy do not need direct access to the Internet at all.

Example setup of a local caching proxy on a vanilla Solaris 10 system:

  # mkdir /var/tmp/pca
  # chown webservd:webservd /var/tmp/pca

This is where patches, READMEs and patchdiag.xref will be stored by
the proxy. Now put the CGI script in place and create a configuration
file:

  # cd /var/apache2/cgi-bin
  # cp /usr/local/bin/pca pca-proxy.cgi
  # chmod 555 pca-proxy.cgi
  # cat > /etc/pca-proxy.conf
  xrefdir=/var/tmp/pca
  patchdir=/var/tmp/pca
  user=XXXXXX
  passwd=YYYYYY
  ^D
  # chown webservd:webservd /etc/pca-proxy.conf
  # chmod 600 /etc/pca-proxy.conf

If the apache2 server is not running yet, create I</etc/apache2/httpd.conf>
and enable the server with I<svcadm>:

  # cp /etc/apache2/httpd.conf-example /etc/apache2/httpd.conf
  # svcadm enable svc:/network/http:apache2

Test the caching proxy on a client:

  ./pca -X . --xrefurl=http://server.domain/cgi-bin/pca-proxy.cgi
  --patchurl=http://server.domain/cgi-bin/pca-proxy.cgi -d 126306-01

The patchdiag.xref and 126301-01.zip will be downloaded by the proxy and
stored in I</var/tmp/pca/> on the server, and both files will be delivered
to the client. If it doesn't work, add I<debug=1> to the pca.conf file
and look at /var/tmp/pca-proxy-debug.txt and /var/apache2/logs/ for details.

When downloading large patches through the proxy, you must ensure that
the web server does not kill I<pca-proxy.cgi> before it has completed
the download from Oracle's patch server. Apache has a I<Timeout> option with a default
value of 300 seconds. Raise that to 1800 seconds to avoid problems.

For large setups, you can build a cascade of local caching proxies by
pointing one proxy at another proxy by setting I<xrefurl> and I<patchurl>
to point at the master proxy in the slave proxies' pca.conf.

As PCA uses the wget command to download patches from the patch server,
make sure that any specially required option is set in I</etc/wgetrc> or
I<$HOME/.wgetrc>. Example: When running the local patch server on a HTTPS
server with a self-signed certificate, I<check-certificate=off> should
be specified in I<wgetrc> on the client.

=head1 UNBUNDLED PATCHES

Usually a patch is related to one or more software packages installed
on a system. Apart from that, there are unbundled patches. They
provide firmware updates for machines, disks, or tape drives and fixes
for software which doesn't come in package format. Currently there is
no way to automatically determine if such patches actually apply to a
system.

The I<unbundled> operand specifies this type of patches.
At first, I<pca -l unbundled> will show a long list of patches.
To reduce this list
to the interesting ones, unnecessary patches can be ignored by using
the I<ignore> option in a PCA configuration file.
For patches you are absolutely not interested in, use an
entry like I<ignore=123456> in the configuration file;
this patch will never be shown again, even if a newer revision of
the patch appears. Patches that are installed in their current revision
should be put with this revision into the configuration file
(e.g. I<ignore=123456-78>).
The patch will show up again when a newer revision is released.

Example: Patch 106121-18 contains the most recent PROM firmware for
Ultra 5/10 workstations. As it's installed on all systems, I put
I<ignore=106121-18> into the configuration file.
When a new revision of the patch
is released, it will show up in I<pca -l unbundled> again.
Patch 118324 is the PROM firmware patch for the Sun Fire V440. As I
don't have such a machine, I put I<ignore=118324> into the
configuration file to ignore this patch completely.

All that PCA can do is to notify of new unbundled patches or patch
revisions. It's on you to decide whether a patch is needed by checking
its README file, and to install it by following the instructions in the
README. Unbundled patches cannot be installed by patchadd or PCA.

=head1 CREATING PATCH REPORTS FOR REMOTE MACHINES

PCA can create a patch report or download patches for a
system which cannot run PCA directly, like stripped-down
systems without perl or an Internet connection. On such systems,
run:

  uname -a > uname.out
  showrev -p > showrev.out
  pkginfo -x > pkginfo.out

On systems with a minimal core installation of Solaris, the I<showrev>
command might not be available. Use I<patchadd -p E<gt> showrev.out>
instead.

Copy the resulting I<*.out> files to a system where PCA is
installed. Use the I<-f DIR> or I<--fromfiles=DIR> option to
point PCA at the location of the input files.
The argument to I<-f> can be a directory
or a file name prefix like I<myhost_>.
This allows collecting I<*.out> files for multiple systems
and telling PCA which ones to read.

If Sun Explorer is used to collect information about Sun systems, a
directory containing Sun Explorer output can be used as the argument
to I<-f> as well.

Other options can be used in combination
with I<-f>. Example: I<pca -f . -d missing> downloads all missing
patches for the remote system.

=head1 LIVE UPGRADE

PCA can be used in combination with Live Upgrade to analyze or install
patches in an inactive boot environment. Use I<lumount> to mount the
BE and PCA's I<--root=DIR> option to set the alternative root directory:

  lumount BE_name
  pca --root=/.alt.BE_name --install
  luumount BE_name

When you're done patching, activate the new BE and reboot with I<init 6>.

PCA always installs the patch for the patch installation utilities
first to avoid possible bugs in I<patchadd>. When patching an inactive
BE, this patch should be installed manually to the active BE, as its
patch installation utilities are used even when I<root=DIR> is set.

=head1 ZONES

PCA can be run both in the global zone or any non-global zone. Patches
installed in the global zone are usually installed in all non-global zones,
too. It's recommended to install patches in the global zone first,
and then run PCA in all non-global zones to check for additionally
needed patches. This is necessary if packages have been added to or
removed from just the global or any non-global zone.

When PCA is run with the I<-G> option, this option is handed through
to patchadd, which will install patches in the current zone only. See the
man page for patchadd for further details.

=head1 THREADS

If PCA is run with the I<--threads=NUM> option, in conjunction with the
download I<-d> or install I<-i> options, PCA will begin downloading multiple
patches in parallel, up to NUM patches at once.  Patches will still be
installed one at a time, in the appropriate order.

The perl version used to run PCA must support threading, otherwise requests
to use threading will be silently ignored. The /usr/bin/perl which comes with
Solaris and perl binaries compiled with the default settings do not
support threading. In that case, the output of I<--help> will indicate that
threads have been disabled.

=head1 UPDATE PCA

Changes to the patch infrastructure by Oracle and problems with
single patches often make updates to PCA necessary. To ease that procedure,
the I<update=TYPE> option can be used. The default is type I<never> - PCA
will never
check for updates. Use the I<check> type to contact the PCA webpage and
check for available updates. Using I<now> will not only check, but also
download and install the updated version of PCA.

With I<auto>, PCA will check for updates automatically once per day,
keeping itself up to date without user intervention. Unlike I<check>
and I<now> which are for interactive usage, this type is best used
in a configuration file.

The default URL to check for updates is
http://www.par.univie.ac.at/solaris/pca/stable/
(official release). It can be set with the I<pcaurl=URL> option.
Set it to
http://www.par.univie.ac.at/solaris/pca/develop/
to check for and update to new development versions of PCA.
You can set I<pcaurl> to point at a local URL
to distribute whatever version in your local network.
If set to point at a local caching proxy, the proxy will check
for updates automatically, keep a local copy of the pca script
in I<patchdir> and deliver it to the client.

Set I<update=auto> in the configuration file for PCA in proxy mode
(I<pca-proxy.cgi>) to make it keep itself up-to-date.

=head1 JUMPSTART

You can use PCA to install patches in the finish script of a jumpstart
install server. Perl is included in the OS image which is booted over
the network for installation starting with Solaris 8. As the machine
will probably not have an Internet connection during installation, you can
either pre-download all necessary patches into a directory accessible
via NFS, or set up a local caching proxy. If you use any http or ftp
url for I<xrefurl> or I<patchurl>, you must put a copy of wget into
the directory that contains your finish script and PCA, and use the
I<wget> option to point PCA at it.

Set I<patchdir> and I<xrefdir> (unless you use I<nocheckxref>) to /tmp
to avoid problems with non-writable directories.  As the OS which gets
installed during jumpstart is mounted at /a, use the I<root> option to
instruct PCA to install patches there.

=head1 EXAMPLES

List all missing patches. This is
the same as running pca without any arguments:

  pca -l missing

List all installed security patches:

  pca -l installeds

Display the README for the current revision of patch 116532:

  pca --readme 116532

Show all installed patches which are marked Bad. You should read the
patch README to find out how to handle a specific bad patch:

  pca -l bad

Download multiple explicitly specified patches, asking for
My Oracle Support Account data when needed:

  pca -d 121308-02 122032

Download and install all missing patches which do not require to reboot
the system in safe mode:

  pca --noreboot --safe --install

Download all missing patches for a remote system. Output from I<uname -a>,
I<showrev -p> and I<pkginfo -x> has been saved to /tmp/myhost_uname.out
etc. before:

  pca -f /tmp/myhost_ -d missing

Check for a new version of PCA and install it:

  pca --update now

A sample configuration file:

  # My Oracle Support Account
  user=myuser@mydomain.org
  passwd=secret
  # Try local patch repositories before the Oracle server
  patchurl=file:/patches http://www.my.org/patches/ oracle
  syslog=user
  safe=1

A sample configuration file for a client of a PCA proxy:

  # Get everything from the proxy
  patchurl=http://www.my.org/patches/pca-proxy.cgi
  xrefurl=http://www.my.org/patches/pca-proxy.cgi

=head1 ENVIRONMENT VARIABLES

All environment variables with the I<PCA_> prefix are evaluated
as options; see CONFIGURATION for details. Furthermore, these environment
variables are used by PCA:

=over

=item PAGER

Path to the command which is used to display patch README
files

=item TMPDIR

During patch installation, patches are extracted under this
directory

=back

=head1 DOWNLOAD ERRORS

If downloads of patches, patch READMEs or the patchdiag.xref
file fail, the displayed error might help to diagnose the problem:

=over

=item Service Error (403)

The user/passwd combination you provided is not correct.

=item You are not entitled to retrieve this content (403)

The user/passwd combination is correct, but the MOS Account does not have
the Support Level required for the requested file. See
SUPPORT LEVELS for more information.

=item Not Found (404)

The requested file does not exist on Oracle's patch server.

=item Server Error, Service Unavailable, Gateway Timeout (5xx)

The Oracle patch server is in a bad state. Retry later.

=back

=head1 EXIT STATUS

The following exit values are returned:

  0  No error

  1  Unknown error

  2  Usage error

  3  Reboot required to continue patch installation

  4  Reboot required

  5  Reboot recommended

=head1 AUTHORS

Martin Paul E<lt>martin.paul@univie.ac.atE<gt>

Thanks to everybody who contributed code or provided feedback:

Andrew Brooks, Bruce Riddle, Damian Hole, Peter Van Eynde,
Richard Whelan, Eugene MacDougal, Peter Schmitz, Fredrik Lundholm,
Dan W. Early, Markus Reger, Constantijn Sikkel, Stephen P. Potter,
Fletcher Cocquyt, Timothy J. Howard, Thomas Bluhm, Frank Doeschner,
Loris Serena, Marion Biallowons, Ricky Chew, Martin R. Korczak,
Imad Soltani, Scott Lucas, Anders Grund, Bernd Senf, Chris Zappala,
Ashley Krelle, Mike Patnode, Mats Larsson, Thomas Maier-Komor,
Willi Burmeister, Stefaan A. Eeckels, Ian Collins, Leptonux,
Joseph Millman, Guenter Zaehle, Frank Fejes, Mark Jeffery,
Alberto da Silva, Mauricio Tavares, Kurt Rabitsch, Jeff Wieland,
Frank Bertels, Steve Meier, Dan Lorenzini, Gerard Henry, Laurent Blume,
Sean Berry, George Moberly, Erik Nordenberg, Mark Ashley, Jim Prescott,
Christian Pelissier, Hugues Sapin, Colin A. White, Dale T. Long,
Christophe Kalt, Bruno Delbono, Nan Liu, Frank Cusack,
Marlon Sanchez-Nunez, Jois Diwakar, Toni Viemero, Jens Larsson,
Gordon D. Gregory, Luis Catacora, Erik Larson, Tim Longo, Mike Borkowski,
Nicolas Goy, William Bonnet, Dave Love, Thomas Brandstetter, Daniel Kunkel,
Gregor Longariva, Miroslav Zubcic, Tim Bradshaw, Chris Quenelle,
Christopher Odenbach, Andy Fiddaman, Peter Sundstrom, Andreas F. Borchert,
Jonah Simandjuntak, Damian Lilley, Chris Ridd, Albert Lee, James Lick,
John Douglass, Andres A. Flores Concepcion, Chris Reece, Toni Viemero,
Timothy Meader, John D. Groenveld, Ceri Davies, Martin Wismer,
Laszlo Kiss, Mike Moya, Leon Koll, Shawn Boots, Mike Wallace,
Robert P. McGraw, Peter Arnold, Matt Kolb, Mike Shackelford, John Dzubera,
Donald Teed, Asif Iqbal, Stephen Nash, Jason Loretz, Bryan Howard, Roman,
Jonathan Hoefker, Daniel Trinkle, Ron Halstead, Rob Fisher, Chris Coffey,
Travis Freeland, Hans-Werner Jouy, Gary Mills, Craig Bell, Mick Russom,
Brian King, Ashley Rowland, Guillermo Castellini, Bryan D. Moorehead,
Mark Scheufele, Corey Becker, David Robson, Kevin Maguire, Mike Wallace,
Marcos Della, Frank Sperber, Horst Scheuermann, Adrian Ulrich, Steve Fox,
David Collodel, Jeremiah Johnson, Erik Schubert, David Sullivan,
Tom Francen, Matthew Scala, Richard Mayebo, Gerald Sinkiewicz,
David Montag, Steve Forman, Jeffrey King, Gerry Van Trieste,
Chris Denneen, Greg Barry, Paul Armstrong, Andreas Fineske,
Eric Kissinger, Torsten Peter, Yevgeniy Averin, Sean Walmsley,
Alexander Skwar, Jeffrey King, Jones Olatunji, Richard Skelton,
Kjetil Torgrim Homme, Brian McNamara, Gerry Sinkiewicz, Kazuyuki Sato,
Mayuresh Kshirsagar, Mauro Mozzarelli, Judy Illeman Gaukel, Petri Kunnari,
William Pool, Steven Faulconer, Rono Jacob, Will Green, Martial Rioux,
Zafar Pravaiz, Romeo Theriault, Fredrich Maney, Ben Szoko, Pietari Hyvarinen,
Roman Pestka, Juergen Mengeling, David S. Bryant, Maciek S., Alexander
Sverdlov, David Coronel, David Groce, Jeff Woolsey, Thomas Marshall,
Allen Eastwood, Mike Busse, Martin Bellenberg, Dennis Clarke,
Dominique Frise, Mark Hopkins, Enda O'Connor, Victor Feng, Peter Englmaier,
Paul B. Henson, Gerry Haskins, Jeff A. Earickson, Stuart Anderson,
Dagobert Michelsen, Simon Bellwood, Ateeq Altaf, Andrew Berry, Julian Davies,
Con Petsoglou, Uwe Wolfram, Micah Cowan, Dan Shaw, Paul Moore, Neal A. Lucier,
Eric Bourgi, Sergiusz Pawlowicz, Paul Van Bommel, Matt Banks, Ray Cromwell,
Jan Holzhueter, Liam Carey, Alex Docauer, Christopher S. Chan, Philip Kime,
Michael Schmarck, Kevin L. Bliss, Thomas Bleek, Albert White, Ron Helzer,
Sergei Haramundanis, Steven M. Christensen, Felix Schattschneider,
Rajiv G Gunja, Jeremy Simpson, Jesse Caldwell, Amy Rich, Jens Elkner,
Stephen Matich, Justus J. Addiss, Fred Chagnon, David French, Don O'Malley,
Stuart F. Biggar, Diana Stockdale, Randal T. Rioux, Todd Koeckeritz,
Matthew Braun, Shaimon Luke, Norman Lyon, Sebastian Kayser, Paul A. Zakas,
Glenn Satchell, Ben Taylor, Brian Geary, Drazen Kacar, Edwin Schwab,
Shahab Khan, Thots Soppannavar, Beth Lancaster, Michael Jackson,
Daniel Pecka, Dirk Lemoisne, Scott L Nishimura, Mike Brown,
Michele Vecchiato, Eugene Olshenbaum, Benny Kleykens, Colin Daly, Rod Holmes,
Jeff Blaine, Tim Frost, Steven M. Falconer, Thomas Gouverneur,
Marcel Hofstetter, Jeremy Daniel.

=head1 MAILING LISTS

Two mailing lists are available:

=over

=item pca-news

This is a one-way list for announcements of new versions and news.
To join, send an empty message to E<lt>pca-news-join@lists.univie.ac.atE<gt>.

=item pca

This is a discussion and support list. Messages from pca-news will be
posted to this list as well. Only members are allowed to post to the list.
To join, send an empty message to
E<lt>pca-join@lists.univie.ac.atE<gt>. To post to the list, send your
message to E<lt>pca@lists.univie.ac.atE<gt>.

=back

=head1 SEE ALSO

=over

=item PCA web site:

http://www.par.univie.ac.at/solaris/pca/

=back

=head1 CHANGES

=head2 Version 20150327-01

 * Add new CA certs
 * Must use --no-check-certificate for Oracle server with wget <= 1.12
 * Verify file type on patch downloads from Oracle server

=head2 Version 20140115-01

 * Add new CA certs for login.oracle.com
 * Use --secure-protocol=TLSv1 with wget on all connections to Oracle server
 * Fix bug in HTML output
 * Whitelist: add 148104, 148105
 * Whitelist: add 150525, 150526

=head2 Version 20130502-01

 * Do not pass on Recommended flag with --minimal option
 * Correct patch obsoletions from installed patches with --minimal option
 * Fix rare bug of certain patches not showing up with --minimal option
 * Remove link to patch README on wesunsolve.net in HTML output
 * Temporary workaround for problem with Oracle server and wget from OpenCSW
 * Whitelist: add 147143, 147144
 * Whitelist: add 147147, 148148, 148027, 148028
 * Whitelist: add 149173, 149174, 149175, 149176
 * Apply check: add 147416, 147419

=head2 Version 20120829-01

 * Check for wget in update function
 * Ignore non-executable wget binaries
 * Whitelist: replace 145957 with 146232
 * Whitelist: replace 145958 with 146233
 * Apply check: add 119303, 119304, 119305
 * Apply check: add 147992, 147993
 * Apply check: add 112762
 * Apply check: add 112443

=head2 Version 20120326-01

 * Fix timing calculation for patch sessions longer than 24 hours
 * Add warning when --minimal is used with anything but missingr
 * When using option "minimal", show that in the "List:" header
 * Always put URL at the end of wget command line
 * Change author's e-mail address
 * Documentation: Recommend use of --minimal with missingr only
 * Whitelist: add 148165, 148166
 * Whitelist: add 147673, 147674
 * Whitelist: add 146399
 * Whitelist: modify 147441
 * Apply check: replace 145786 with 146068
 * Apply check: replace 125952/125953 with 147673/147674

=head2 Version 20120119-01

 * Ignore missing showrev/patchadd on Solaris 11
 * Remove useless attempt to guess file type with zip files from Oracle
 * Documentation: add information about "minimal" option
 * Whitelist: add 115336, 115337
 * Whitelist: modify 147440, 147441
 * Update list of contributors

=head2 Version 20111018-01

 * Allow multiple URLs and paths for xrefurl/patchurl options
 * Add special keyword "oracle" for xrefurl/patchurl options
 * Catch unknown type of URLS in xrefurl/patchurl options
 * Change behaviour of "ignore" option
 * Add new format specifier (%d) to show patch release date
 * Add link to patch README on wesunsolve.net in HTML output
 * Fix wrong behaviour when ignoring required patch revisions
 * Workaround for a bug in wget 1.13.3
 * Show required patches which are ignored in debug output
 * Documentation: Update description of the "ignore" option
 * Documentation: Remove information about "dontask"
 * Whitelist: add 147714
 * Whitelist: add 147268, 147269
 * Whitelist: add 147440, 147441
 * Whitelist: add 119906, 119907
 * Update list of contributors

When xrefurl/patchurl is set and the requested file cannot be found
there, PCA will not look at Oracle's server by default anymore. Get
the old behaviour by adding the special keyword "oracle" at the end
of xrefurl/patchurl (which now accept multiple URLs).

Patches which are specified via the ignore option are now ignored
even when they are required by other patches.

=head2 Version 20110812-01

 * Always set proxy both for HTTP and HTTPS when wgetproxy is set
 * Recognize new obscure way of Oracle server saying "login failed"
 * New option to unzip patches (--unzip)
 * Remove useless attempt to download tar.Z file from Oracle
 * Fix error about "Use of initialized value"
 * Update list of contributors

=head2 Version 20110805-02

 * Deprecate option supplevel after Oracle broke query interface
 * Fix showing errors when running pca proxy in debug mode
 * Whitelist: add 144500, 144501
 * Whitelist: replace 143647/143648 with 145957/145958
 * Whitelist: replace 143957/143958 with 146489/146490
 * Whitelist: replace 143645/143646 with 146232/146233
 * Whitelist: add 146673, 146674
 * Whitelist: modify 144489
 * Whitelist: remove obsolete patches
 * Whitelist: remove patches for products which reached EOSL
 * Apply check: add 147056
 * Apply check: add 142633, 142634
 * Apply check: remove patches for products which reached EOSL
 * Update list of contributors

=head2 Version 20110329-01

 * Try patch downloads in tar.Z format as well from Oracle
 * Fix handling of empty input on user/password prompt
 * Fix a rare warning about uninitialized value
 * Show size of patchdiag.xref in debug output
 * Whitelist: add 144488, 144489
 * Whitelist: add 145042, 145043
 * Whitelist: remove obsolete patches
 * Apply check: add 146363, 146364
 * Apply check: add 113044, 114476, 111846, 114475
 * Update list of contributors

=head2 Version 20101221-01

 * New option to show support levels of a given MOS Account (--supplevel)
 * Send authentication to Oracle server without being asked
 * Use links to getupdates.oracle.com in HTML output
 * Rename option sshost to ohost
 * Remove long deprecated option (--localurl)
 * Remove unused debug message about passing on recommended status
 * Documentation: Add information about SUPPORT LEVELS
 * Documentation: Adapt DOWNLOAD ERRORS to Oracle server's answers
 * Documentation: Refer to pca as PCA
 * Update list of contributors

=head2 Version 20101213-01

 * Use getupdates.oracle.com as patch server
 * Use standard wget authentication options with Oracle
 * Remove option to download patches in JAR format (--jar)
 * Include and use VeriSign certificate for HTTPS downloads from Oracle
 * Remove unused VeriSign certificate for sunsolve.sun.com
 * Documentation: Replace Sun Online Account with My Oracle Support Account
 * Documentation: Replace sunsolve.sun.com with getupdates.oracle.com
 * Documentation: Replace Sun with Oracle
 * Whitelist: add 144537
 * Apply check: add 145786

Attention: A My Oracle Support Account is required instead of a
Sun Online Account now. All downloads from Oracle's patch server
require a wget binary with SSL/HTTPS support. Downloads of patches
in JAR format are not supported by Oracle anymore.

=head2 Version 20100910-01

 * Ignore patch dependencies when only full patch IDs/revisions are used
 * Fix handling of duplicate patch IDs (123456-XX, 123456-YY) as operands
 * Documentation: fix small formatting issue
 * Whitelist: add 143957, 143958, 145098, 145099
 * Whitelist: add 143645, 143646, 142933, 142934, 142909, 142910
 * Whitelist: add 143647, 143648, 144188, 144189
 * Whitelist: remove obsolete patches
 * Apply check: add 139610, 139611
 * Apply check: add 143075, 143076, 143077, 143078, 143079
 * Apply check: add 143310, 143311, 143312, 143313, 143314
 * Apply check: add 143320, 143321, 143322, 143323, 143324
 * Apply check: add 143053
 * Update list of contributors

=head2 Version 20100727-01

 * Skip reading of input files only when --readme is the sole action
 * Do not show cleartext/base64 user/passwd in debug output
 * Move pca-proxy-debug.txt from /tmp to /var/tmp
 * Whitelist: add 138261, 138262, 145027, 145028 and 141511
 * Apply check: add 140993 and 140994
 * Apply check: remove 139335, 139336, 139337, 139338

=head2 Version 20100607-01

 * Pass on Recommended status from obsolete patches/revisions
 * Fix handling of non-standard lines in patchdiag.xref
 * Add specifier %o for --format to show the OS column from xref
 * Fix handling of multiple use of the same specifier with --format
 * New experimental option for recommended cluster support (--minimal)
 * Update list of contributors

Attention: There has been a change in the format of patchdiag.xref
regarding the Recommended status of patches. The changes in this
version are required to maintain pca's behaviour of always showing
the most current revision of any patch carrying the Recommended flag.
See: http://blogs.sun.com/patch/entry/merging_the_solaris_recommended_and

=head2 Version 20100514-01

 * Fix for configuration file being read twice
 * New option to feed options directly to wget (--wgetopt)
 * Pass on Recommended status from non-obsolete revisions
 * Show program name and current working directory in debug output
 * Documentation: Information about patch installation utilities patches
 * Whitelist: add 141876, 141877, 125388 and 125389
 * Whitelist: remove obsolete patches
 * Apply check: remove 127683 and 127684, add 143323 and 143324
 * Update list of contributors

=head2 Version 20100309-02

 * Show timing information and patch counts during patch installation
 * Do not recommend/require reboot when noreboot option is used
 * Work better on non-Solaris machines (e.g. Linux)
 * Documentation: A Sun Service Plan is required for all patch downloads
 * Documentation: Description of timing information and patch counts
 * Documentation: Fix Live Upgrade command sequence
 * Documentation: Fix quotation marks
 * Whitelist: add 141878, 141879, 142901
 * Whitelist: remove obsolete patches
 * Update list of contributors

=head2 Version 20091216-02

 * Use internal functions instead of File::Temp module
 * Fix perl error (modification of a read-only value attempted)
 * Update list of contributors

=head2 Version 20091210-01

 * Make behaviour of the askauth option the default and deprecate it
 * Never ask for SOA data if user option is set to dontask
 * Use temporary wgetrc instead of command line option to hide SOA data
 * Identify patch utility patches dynamically to replace hardcoded list
 * Ask for SOA data in proxy mode, when needed
 * Send SOA data to local caching proxy via custom HTTP header
 * Set user and passwd from custom X_PCA_ HTTP headers in proxy mode
 * Return HTTP error 401 instead of 500 when proxy needs SOA data
 * Return HTTP error 404 instead of 500 when proxy can't find a file
 * Be more verbose when trying downloads from SunSolve
 * Show more detailed error message on download failures
 * Safe creation of temporary files/dirs to avoid race condition
 * Show output from patchadd synchronously in debug mode
 * Catch wget startup error
 * Documentation: Add list of possible causes for download failures
 * Documentation: Add information about Live Upgrade
 * Whitelist: add 128402, 137048, 141525
 * Whitelist: remove obsolete patches
 * Update list of contributors

=head2 Version 20091030-01

 * New option to skip check for UID 0 (--norootchk)
 * Change URL used to download patchdiag.xref with HTTPS
 * Show debug output on stderr instead of stdout
 * Do not append "/" to local URL if last character is "="
 * Workaround for problem with safe mode and DAP/turbo-packaging
 * Whitelist: add 140119, 142084, 142085
 * Whitelist: add 141444, 141445, 141874, 141875
 * Apply check: add 136799, 136800
 * Apply check: add 118605, 118607, 118609, 118611, 118613, 118615
 * Update list of contributors

=head2 Version 20090827-01

 * Find the newest wget binary with the best protocol support
 * Change URL used to download patch READMEs
 * Prefer HTTPS for patchdiag.xref download
 * Use HTTPS for patch and README downloads
 * Ignore and deprecate ssprot option

=head2 Version 20090723-01

 * Fix for wgetproxy option not being honored when HTTPS is used
 * New option to disable patch dependency resolution (--nodep)
 * Fix typo in error message
 * Documentation: Posting to the pca mailing list restricted to members
 * Apply check: remove obsolete patches
 * Update list of contributors

=head2 Version 20090408-01

 * Use HTTPS as default when connecting to SunSolve if wget supports it
 * Use arch from pkginfo instead of uname to check if a patch applies
 * Allow both directory or file to be specified with the wget option
 * Show setting of root option with patch install message in syslog
 * Ignore unnecessary error output from pkgparam
 * Documentation: Mention that --ignore and --stop are sometimes ignored
 * Apply check: remove obsolete patches
 * Update list of contributors

=head2 Version 20090224-01

 * Allow search patterns for synopsis to be used with --ignore
 * Maintain last modification time on patchdiag.xref and pca
 * Add Last-Modified header in local caching proxy mode
 * Preserve last modification time on pca update
 * Maintain timestamps when copying files from file:/ URLs
 * New option to download patches in JAR format (--jar)
 * Fix recognition of jar files
 * Do not show reboot recommendation message if --root=DIR is set
 * Make space part of the option value when used in configuration file
 * Fix safe option for ill-formatted README file
 * Apply check: add 139335, 139336, 139337, 139338
 * Apply check: add 123919, 123920, 123921, 123923
 * Apply check: add 113120, 113121, 113122, 113123
 * Apply check: add 116687, 116688, 116689, 119300, 119301, 119302
 * Apply check: add 120108, 120109, 120110, 123200, 123201, 123202
 * Apply check: add 123827, 123828, 123829, 139345, 139346, 139347
 * Apply check: add 139548, 139549
 * Update list of contributors

=head2 Version 20081218-01

 * Enable syslog messages to daemon.notice by default
 * Enhance possible values for syslog option
 * Log sample message to syslog in debug mode
 * New generic handling of unknown, non-Sun patches
 * Documentation: Add cp command in local server setup example
 * Rename internal function err() to avoid keyword clash with recent perl
 * Mark patch 114147 as BAD
 * Whitelist: add 137137, 137138, 121308, 121309, 138270
 * Whitelist: remove obsolete patch
 * Apply check: add 110936, 110937, 110938, 110971, 110972, 110973
 * Apply check: add 118386, 118387, 118388, 118389
 * Apply check: add 118828, 118829
 * Apply check: add 118836, 118837, 118838, 118839
 * Apply check: add 127680, 127681, 127682, 127683, 127684
 * Apply check: add 138550, 138551, 138552, 138553, 138554
 * Update list of contributors

=head2 Version 20081024-01

 * Read only pca-proxy.conf (not pca.conf) in proxy mode
 * Provide more detailed exit status
 * Include patch count and sum of patch ages in header
 * Fix handling of downloaded files that are too short
 * Check whether patch already exists before announcing download
 * Fix handling of PTF/ACSLS patches
 * Read architecture information from pkginfo output
 * Accept wrong entries in the arch column in patchdiag.xref
 * Handle special characters in package version string
 * Fix erroneous behaviour with checking for patch existance
 * Simplify internal handling of extra patch requirements
 * Calculate patch age only once
 * Apply check: add 116413, 119775, 116831, 116832
 * Update list of contributors

=head2 Version 20080911-01

 * Remove check for patches which are only partly installed

=head2 Version 20080909-01

 * Check for patches which are only partly installed
 * Fix bug with missing patches with multiple versions of the same package
 * Log failed patch install to syslog
 * Fix minage option being one day off
 * Include and use VeriSign certificate for HTTPS downloads from SunSolve
 * Include and use CyberTrust certificate for HTTPS downloads from pca home
 * Simplify patch download and pca update code
 * Simplify patch README download code
 * Simplify patchdiag.xref download code
 * Add some debug code
 * Fix coding error
 * Code cleanup
 * Documentation: Better describe what the noheader option does
 * Fix required patches which were never released: 125486, 125487, 114431
 * Fix required patches which were never released: 126677, 126678
 * Apply check: modify 119313, 119314
 * Update list of contributors

Today pca turns 5 years; version 1.0 was published first on 2003/09/09.

Thanks to all of you for the large amount of positive feedback I've
received during the last years!

=head2 Version 20080729-01

 * Workaround for 120011/120012 requiring obsolete patches 122660/122661
 * Fix a bug when using current version of wget with https
 * Enhance checks for empty or corrupt patchdiag.xref file
 * New default URL setting for pcaurl
 * Apply check: add 121708, 121709, 121710, 125848, 125849, 125850
 * Update list of contributors

=head2 Version 20080626-01

 * New option to list patches with a maximum age (--maxage=DAYS)
 * Create DIR/reconfigure (not /reconfigure) when using --root=DIR
 * Don't show ignorable error message from showrev
 * Fix required patches which were never released: 125077, 125078
 * Whitelist: add 120185, 120186
 * Whitelist: remove obsolete patches
 * Apply check: add 137112, 119252, 119253
 * Apply check: add 136987, 136986
 * Apply check: add 127553, 127554
 * Apply check: remove obsolete patches
 * Update list of contributors

=head2 Version 20080519-01

 * Fix a bug where pca fails to run when threads option is used
 * Use locally existing patches in jar format
 * Read configuration file immediately when cffile option is seen
 * Enhance performance with hundreds of patch IDs as operands
 * Fix hanging unzip when no diskspace is left
 * Show timestamp in debug mode when patchadd is started
 * Remove duplicate debug message
 * Documentation: Add note about possible requirement of wgetrc settings
 * Whitelist: add 137093, 137094
 * Apply check: fix 119381
 * Apply check: add 125445, 125446
 * Cosmetic changes
 * Update list of contributors

=head2 Version 20080507-01

 * Add option for concurrent patch downloads (--threads=NUM)
 * New option to set sunsolve access protocol to HTTPS (--ssprot=PROT)
 * Ignore HTML tags in patchdiag.xref
 * Honor wgetproxy option for non-SunSolve URLs as well
 * Read ../etc/pca-proxy.conf in proxy mode
 * Fix wget version detection under Red Hat
 * Make safe option work with ill-formatted README files
 * Whitelist: add 137274, 137275
 * Whitelist: add 127755, 127756, 128307
 * Whitelist: add 127127, 127128
 * Apply check: add 117429, 118386, 118387, 118388, 118389
 * Apply check: add 118828, 118829, 118836, 118837, 118838, 118839, 118840
 * Apply check: add 120376, 120377, 120378, 120379, 124689, 124690
 * Apply check: add 116338, 116339, 118383, 118384, 125698, 125699
 * Apply check: add 111857, 114176
 * Apply check: add 119380, 119381
 * Update list of contributors

=head2 Version 20080311-01

 * Try to download patchdiag.xref from alternative sunsolve URL
 * Add hack to make pca work with wget v1.11
 * Add new format specifiers for patch count (%n) and total patches (%t)
 * Show info header even if no patches are listed
 * Fix bug with pca not finding its configuration file in some cases
 * Fix warning about use of uninitialized value
 * Documentation: Add information about mailing lists
 * Whitelist: add 127718
 * Apply check: add 127719
 * Update list of contributors

=head2 Version 20080131-01

 * New option to display man page (-m/--man)
 * Make patch utilities patches appear at the top of the list
 * Create /reconfigure after patch installation if needed
 * Show correct reboot command in patch installation summary (init 6)
 * Allow specifying negative patterns with the pattern option
 * Honore ignore options even if patch IDs are specified explicitely
 * Make update option work with pcaurl set to a local caching proxy
 * Make auto update work with pca in proxy mode
 * Documentation format fixes
 * Whitelist: add 127718
 * Whitelist: remove obsolete patch
 * Apply check: add 126356, 126357
 * Apply check: add 106514, 106515, 108049, 108050, 108879, 108881
 * Apply check: add 109120, 109121, 109413, 109414, 117010, 117011
 * Apply check: add 117784, 117785, 118195, 118196, 118263, 118264
 * Apply check: add 118950, 118951, 123254, 124590
 * Apply check: add 124480, 124481, 124482
 * Update list of contributors

=head2 Version 20080109-01

 * Read /etc/pca-proxy.conf and ./pca-proxy.conf in proxy mode
 * New option to specify additional configuration files (--cffile=FILE)
 * Allow negating boolean options on the command line with --no-option
 * Documentation: Add information about the Timeout option in Apache
 * Whitelist: add 125082, 125890, 128624
 * Whitelist: remove obsolete patch
 * Apply check: add SAM-FS and QFS patches

Use /etc/pca-proxy.conf or pca-proxy.conf in the same directory as
the CGI script from now on. For downward compatibility pca-proxy.cgi
will still read pca.conf in the standard locations, but this is
deprecated.

=head2 Version 20071214-01

 * Enhance check for circular patch dependencies
 * Enhance error handling
 * Update list of contributors
 * Whitelist: add 118717, 127111, 127112

=head2 Version 20071115-01

 * Streamline patch downloads from local caching proxy
 * More verbose output during downloads and patch installation
 * Complete code redesign of all download functions
 * Try to download patchdiag.xref from sunsolve without SOA data
 * Always keep backup copy of patchdiag.xref before trying download
 * Use downloaded copy of patchdiag.xref if date is equal to backup copy
 * Always check if downloaded copy of xref file is newer than local copy
 * Restore backup copy of patchdiag.xref if pca is interrupted
 * Correctly handle SOA password with # sign in configuration file
 * Add trailing slash to download URL if missing
 * Show wget version in debug output
 * Fix bug when installing patch using previously unpacked patch directory
 * Change implementation of file type recognition
 * Fix perl warning
 * Update list of contributors

Attention: There has been a change in the protocol used to download
patches from the local caching proxy. Make sure to update both pca
and pca-proxy.cgi.

The output format of pca has been changed to give more detailed information
about download sources and patch installation.

SunSolve has changed in a way that download of the patchdiag.xref file
is possible without a Sun Online Account again. pca now tries both with
and without SOA.

=head2 Version 20071023-01

 * Change nobackup option to accept a patch ID or "all" as argument
 * Preserve local copy of patchdiag.xref if sunsolve copy is older
 * New option to set sunsolve hostname or IP address (--sshost=HOST)
 * Honor setting of nocheckxref option in proxy mode
 * Detect absolute path names for xrefdir/patchdir under Windows
 * Use "--execute cache=off" instead of "--cache=off" with nocache
 * Show patchadd command in debug output
 * Fix debug message shown when safe option is used
 * Remove temporary entry for 126509 which was missing from xref
 * Apply check: add 123202
 * Apply check: add 123827, 123828, 123829
 * Apply check: add 125760, 125761, 125762

The nobackup option requires an argument now. Instead of --nobackup
use --nobackup=all, or specify selected (e.g. large) patches in
multiple nobackup options.

SunSolve is sometimes delivering out-of-date versions of the
patchdiag.xref file. pca now checks the date in the header and
will not overwrite a more recent local copy with an outdated file
from SunSolve.

=head2 Version 20071011-02

 * A Sun Online Account is needed to access patchdiag.xref
 * Modify askauth to ask for authentication data when needed
 * Use same URL for patch README in HTML output with and without SOA
 * Fix bug with update showing old list of changes
 * Fix typo in reconfiguration message
 * Documentation: Clarify information about ignore option
 * Whitelist: add 121429, 119757, 119758, 125367, 125368
 * Whitelist: modify 121428

With a recent change to SunSolve, a Sun Online Account is now required
to allow pca downloading the patchdiag.xref file. The askauth option
has been modified to ask for the Sun Online Account in that case, too.

=head2 Version 20071005-03

 * Add documentation about using pca in a jumpstart finish script
 * Whitelist: modify 120011
 * Fix small bug with installing Sun Studio 11 patches on Solaris 10

=head2 Version 20071002-01

 * New option to allow pca to update itself (--update=TYPE)
 * Code cleanup and performance enhancements
 * Deliver files in proxy mode directly without HTTP redirect
 * Write debug output to file in proxy mode
 * Fix a problem with timelocal when running pca under Windows
 * Fix obscure bug with --safe option and pathnames with commas
 * Add option to stop after a specified patch ID (--stop=ID)
 * Allow patch proxy to download files from another patch proxy
 * Revert to old mechanism of specifying user and password with wget
 * Include documentation in pca
 * Handle relative path names in xrefdir correctly
 * Whitelist: add 120011, 125369, 120012, 125216, 125370
 * Whitelist: modify 118833
 * Whitelist: remove obsolete patches
 * Apply check: add 125950, 125951, 125952, 125953
 * Apply check: add 121430, 121431, 121428
 * Apply check: add 125276, 125277, 125278
 * Apply check: remove obsolete patches

There is a new version scheme, consisting of the date in ISO format plus a
serial number. The same scheme is used for official and development releases.
A new option has been added (update=TYPE) which allows pca to check for and
install new versions of itself. See UPDATE PCA in the documentation. The
documentation is now included in POD format in pca. Use
I</usr/perl5/bin/perldoc pca> to view it.

There are some enhancements to pca in proxy mode. You can setup a cascade
of local proxies by pointing one proxy at another. The xrefdir and patchdir
are honored now in proxy mode, so you can keep the cache directory out of
the document root of your web server and use an existing cgi-bin directory.
Debugging a proxy is simplified; when the debug option is set, debug output
will be written to a file.

=cut

# O=VeriSign Trust Network, OU=VeriSign International Server CA - Class 3
-----BEGIN CERTIFICATE-----
MIIDgzCCAuygAwIBAgIQRvzrurTQLw+SYJgjP5MHjzANBgkqhkiG9w0BAQUFADBf
MQswCQYDVQQGEwJVUzEXMBUGA1UEChMOVmVyaVNpZ24sIEluYy4xNzA1BgNVBAsT
LkNsYXNzIDMgUHVibGljIFByaW1hcnkgQ2VydGlmaWNhdGlvbiBBdXRob3JpdHkw
HhcNOTcwNDE3MDAwMDAwWhcNMTYxMDI0MjM1OTU5WjCBujEfMB0GA1UEChMWVmVy
aVNpZ24gVHJ1c3QgTmV0d29yazEXMBUGA1UECxMOVmVyaVNpZ24sIEluYy4xMzAx
BgNVBAsTKlZlcmlTaWduIEludGVybmF0aW9uYWwgU2VydmVyIENBIC0gQ2xhc3Mg
MzFJMEcGA1UECxNAd3d3LnZlcmlzaWduLmNvbS9DUFMgSW5jb3JwLmJ5IFJlZi4g
TElBQklMSVRZIExURC4oYyk5NyBWZXJpU2lnbjCBnzANBgkqhkiG9w0BAQEFAAOB
jQAwgYkCgYEA2IKA6NYZAn0fhRg5JaJlK+G/1AXTvOY2O6rwTGxbtueqPHNFVbLx
veqXQu2aNAoV1Klc9UAl3dkHwTKydWzEyruj/lYncUOqY/UwPpMo5frxCTvzt01O
OfdcSVq4wR3Tsor+cDCVQsv+K1GLWjw6+SJPkLICp1OcTzTnqwSye28CAwEAAaOB
4zCB4DAPBgNVHRMECDAGAQH/AgEAMEQGA1UdIAQ9MDswOQYLYIZIAYb4RQEHAQEw
KjAoBggrBgEFBQcCARYcaHR0cHM6Ly93d3cudmVyaXNpZ24uY29tL0NQUzA0BgNV
HSUELTArBggrBgEFBQcDAQYIKwYBBQUHAwIGCWCGSAGG+EIEAQYKYIZIAYb4RQEI
ATALBgNVHQ8EBAMCAQYwEQYJYIZIAYb4QgEBBAQDAgEGMDEGA1UdHwQqMCgwJqAk
oCKGIGh0dHA6Ly9jcmwudmVyaXNpZ24uY29tL3BjYTMuY3JsMA0GCSqGSIb3DQEB
BQUAA4GBAECOSZeWinPdjk3vPmG3yqBirfQOCrt1PeJu2CzHv/S5jDabyqLQnHJG
OfamggNlEcS8vy2m9dk7CrWY+rN4uR7yK0xi1f2yeh3fM/1z+aXYLYwq6tH8sCi2
6UlIE0uDihtIeyT3ON5vQVS4q1drBt/HotSp9vE2YoCI8ot11oBx
-----END CERTIFICATE-----

# O=VeriSign, Inc., OU=Class 3 Public Primary Certification Authority
-----BEGIN CERTIFICATE-----
MIICPDCCAaUCEHC65B0Q2Sk0tjjKewPMur8wDQYJKoZIhvcNAQECBQAwXzELMAkG
A1UEBhMCVVMxFzAVBgNVBAoTDlZlcmlTaWduLCBJbmMuMTcwNQYDVQQLEy5DbGFz
cyAzIFB1YmxpYyBQcmltYXJ5IENlcnRpZmljYXRpb24gQXV0aG9yaXR5MB4XDTk2
MDEyOTAwMDAwMFoXDTI4MDgwMTIzNTk1OVowXzELMAkGA1UEBhMCVVMxFzAVBgNV
BAoTDlZlcmlTaWduLCBJbmMuMTcwNQYDVQQLEy5DbGFzcyAzIFB1YmxpYyBQcmlt
YXJ5IENlcnRpZmljYXRpb24gQXV0aG9yaXR5MIGfMA0GCSqGSIb3DQEBAQUAA4GN
ADCBiQKBgQDJXFme8huKARS0EN8EQNvjV69qRUCPhAwL0TPZ2RHP7gJYHyX3KqhE
BarsAx94f56TuZoAqiN91qyFomNFx3InzPRMxnVx0jnvT0Lwdd8KkMaOIG+YD/is
I19wKTakyYbnsZogy1Olhec9vn2a/iRFM9x2Fe0PonFkTGUugWhFpwIDAQABMA0G
CSqGSIb3DQEBAgUAA4GBALtMEivPLCYATxQT3ab7/AoRhIzzKBxnki98tsX63/Do
lbwdj2wsqFHMc9ikwFPwTtYmwHYBV4GSXiHx0bH/59AhWM1pF+NEHJwZRDmJXNyc
AA9WjQKZ7aKQRUzkuxCkPfAyAw7xzvjoyVGM5mKf5p/AfbdynMk2OmufTqj/ZA1k
-----END CERTIFICATE-----

# O=GTE Corporation, CN=GTE CyberTrust Global Root
-----BEGIN CERTIFICATE-----
MIICWjCCAcMCAgGlMA0GCSqGSIb3DQEBBAUAMHUxCzAJBgNVBAYTAlVTMRgwFgYD
VQQKEw9HVEUgQ29ycG9yYXRpb24xJzAlBgNVBAsTHkdURSBDeWJlclRydXN0IFNv
bHV0aW9ucywgSW5jLjEjMCEGA1UEAxMaR1RFIEN5YmVyVHJ1c3QgR2xvYmFsIFJv
b3QwHhcNOTgwODEzMDAyOTAwWhcNMTgwODEzMjM1OTAwWjB1MQswCQYDVQQGEwJV
UzEYMBYGA1UEChMPR1RFIENvcnBvcmF0aW9uMScwJQYDVQQLEx5HVEUgQ3liZXJU
cnVzdCBTb2x1dGlvbnMsIEluYy4xIzAhBgNVBAMTGkdURSBDeWJlclRydXN0IEds
b2JhbCBSb290MIGfMA0GCSqGSIb3DQEBAQUAA4GNADCBiQKBgQCVD6C28FCc6HrH
iM3dFw4usJTQGz0O9pTAipTHBsiQl8i4ZBp6fmw8U+E3KHNgf7KXUwefU/ltWJTS
r41tiGeA5u2ylc9yMcqlHHK6XALnZELn+aks1joNrI1CqiQBOeacPwGFVw1Yh0X4
04Wqk2kmhXBIgD8SFcd5tB8FLztimQIDAQABMA0GCSqGSIb3DQEBBAUAA4GBAG3r
GwnpXtlR22ciYaQqPEh346B8pt5zohQDhT37qw4wxYMWM4ETCJ57NE7fQMh017l9
3PR2VX2bY1QY6fDq81yx2YtCHrnAlU66+tXifPVoYb+O7AWXX1uw16OFNMQkpw0P
lZPvy5TYnh+dXIVtx6quTx8itc2VrbqnzPmrC3p/
-----END CERTIFICATE-----

# VeriSign Class 3 International Server CA - G3
-----BEGIN CERTIFICATE-----
MIIGKTCCBRGgAwIBAgIQZBvoIM4CCBPzLU0tldZ+ZzANBgkqhkiG9w0BAQUFADCB
yjELMAkGA1UEBhMCVVMxFzAVBgNVBAoTDlZlcmlTaWduLCBJbmMuMR8wHQYDVQQL
ExZWZXJpU2lnbiBUcnVzdCBOZXR3b3JrMTowOAYDVQQLEzEoYykgMjAwNiBWZXJp
U2lnbiwgSW5jLiAtIEZvciBhdXRob3JpemVkIHVzZSBvbmx5MUUwQwYDVQQDEzxW
ZXJpU2lnbiBDbGFzcyAzIFB1YmxpYyBQcmltYXJ5IENlcnRpZmljYXRpb24gQXV0
aG9yaXR5IC0gRzUwHhcNMTAwMjA4MDAwMDAwWhcNMjAwMjA3MjM1OTU5WjCBvDEL
MAkGA1UEBhMCVVMxFzAVBgNVBAoTDlZlcmlTaWduLCBJbmMuMR8wHQYDVQQLExZW
ZXJpU2lnbiBUcnVzdCBOZXR3b3JrMTswOQYDVQQLEzJUZXJtcyBvZiB1c2UgYXQg
aHR0cHM6Ly93d3cudmVyaXNpZ24uY29tL3JwYSAoYykxMDE2MDQGA1UEAxMtVmVy
aVNpZ24gQ2xhc3MgMyBJbnRlcm5hdGlvbmFsIFNlcnZlciBDQSAtIEczMIIBIjAN
BgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEAmdacYvAV9IGaQQhZjxOdF8mfUdza
sVLv/+NB3eDfxCjG4615HycQmLi7IJfBKERBD+qpqFLPTU4bi7u1xHbZzFYG7rNV
ICreFY1xy1TIbxfNiQDk3P/hwB9ocenHKS5+vDv85burJlSLZpDN9pK5MSSAvJ5s
1fx+0uFLjNxC+kRLX/gYtS4w9D0SmNNiBXNUppyiHb5SgzoHRsQ7AlYhv/JRT9Cm
mTnprqU/iZucff5NYAclIPe712mDK4KTQzfZg0EbawurSmaET0qO3n40mY5o1so5
BptMs5pITRNGtFghBMT7oE2sLktiEuP7TfbJUQABH/weaoEqOOC5T9YtRQIDAQAB
o4ICFTCCAhEwEgYDVR0TAQH/BAgwBgEB/wIBADBwBgNVHSAEaTBnMGUGC2CGSAGG
+EUBBxcDMFYwKAYIKwYBBQUHAgEWHGh0dHBzOi8vd3d3LnZlcmlzaWduLmNvbS9j
cHMwKgYIKwYBBQUHAgIwHhocaHR0cHM6Ly93d3cudmVyaXNpZ24uY29tL3JwYTAO
BgNVHQ8BAf8EBAMCAQYwbQYIKwYBBQUHAQwEYTBfoV2gWzBZMFcwVRYJaW1hZ2Uv
Z2lmMCEwHzAHBgUrDgMCGgQUj+XTGoasjY5rw8+AatRIGCx7GS4wJRYjaHR0cDov
L2xvZ28udmVyaXNpZ24uY29tL3ZzbG9nby5naWYwNAYDVR0lBC0wKwYIKwYBBQUH
AwEGCCsGAQUFBwMCBglghkgBhvhCBAEGCmCGSAGG+EUBCAEwNAYIKwYBBQUHAQEE
KDAmMCQGCCsGAQUFBzABhhhodHRwOi8vb2NzcC52ZXJpc2lnbi5jb20wNAYDVR0f
BC0wKzApoCegJYYjaHR0cDovL2NybC52ZXJpc2lnbi5jb20vcGNhMy1nNS5jcmww
KAYDVR0RBCEwH6QdMBsxGTAXBgNVBAMTEFZlcmlTaWduTVBLSS0yLTcwHQYDVR0O
BBYEFNebfNgioBX33a1fzimbWMO8RgC1MB8GA1UdIwQYMBaAFH/TZafC3ey78DAJ
80M5+gKvMzEzMA0GCSqGSIb3DQEBBQUAA4IBAQBxtX1zUkrd1000Ky6vlEalSVAC
T/gvF3DyE9wfIYaqwk98NzzURniuXXhv0bpavBCrWDbFjGIVRWAXIeLVQqh3oVXY
QwRR9m66SOZdTLdE0z6k1dYzmp8N5tdOlkSVWmzWoxZTDphDzqS4w2Z6BVxiEOgb
Ett9LnZQ/9/XaxvMisxx+rNAVnwzeneUW/ULU/sOX7xo+68q7jA3eRaTJX9NEP9X
+79uOzMh3nnchhdZLUNkt6Zmh+q8lkYZGoaLb9e3SQBb26O/KZru99MzrqP0nkzK
XmnUG623kHdq2FlveasB+lXwiiFm5WVu/XzT3x7rfj8GkPsZC9MGAht4Q5mo
-----END CERTIFICATE-----

# VerSign Class 3 Public Primary Certification Authority - G5
-----BEGIN CERTIFICATE-----
MIIE0zCCA7ugAwIBAgIQGNrRniZ96LtKIVjNzGs7SjANBgkqhkiG9w0BAQUFADCB
yjELMAkGA1UEBhMCVVMxFzAVBgNVBAoTDlZlcmlTaWduLCBJbmMuMR8wHQYDVQQL
ExZWZXJpU2lnbiBUcnVzdCBOZXR3b3JrMTowOAYDVQQLEzEoYykgMjAwNiBWZXJp
U2lnbiwgSW5jLiAtIEZvciBhdXRob3JpemVkIHVzZSBvbmx5MUUwQwYDVQQDEzxW
ZXJpU2lnbiBDbGFzcyAzIFB1YmxpYyBQcmltYXJ5IENlcnRpZmljYXRpb24gQXV0
aG9yaXR5IC0gRzUwHhcNMDYxMTA4MDAwMDAwWhcNMzYwNzE2MjM1OTU5WjCByjEL
MAkGA1UEBhMCVVMxFzAVBgNVBAoTDlZlcmlTaWduLCBJbmMuMR8wHQYDVQQLExZW
ZXJpU2lnbiBUcnVzdCBOZXR3b3JrMTowOAYDVQQLEzEoYykgMjAwNiBWZXJpU2ln
biwgSW5jLiAtIEZvciBhdXRob3JpemVkIHVzZSBvbmx5MUUwQwYDVQQDEzxWZXJp
U2lnbiBDbGFzcyAzIFB1YmxpYyBQcmltYXJ5IENlcnRpZmljYXRpb24gQXV0aG9y
aXR5IC0gRzUwggEiMA0GCSqGSIb3DQEBAQUAA4IBDwAwggEKAoIBAQCvJAgIKXo1
nmAMqudLO07cfLw8RRy7K+D+KQL5VwijZIUVJ/XxrcgxiV0i6CqqpkKzj/i5Vbex
t0uz/o9+B1fs70PbZmIVYc9gDaTY3vjgw2IIPVQT60nKWVSFJuUrjxuf6/WhkcIz
SdhDY2pSS9KP6HBRTdGJaXvHcPaz3BJ023tdS1bTlr8Vd6Gw9KIl8q8ckmcY5fQG
BO+QueQA5N06tRn/Arr0PO7gi+s3i+z016zy9vA9r911kTMZHRxAy3QkGSGT2RT+
rCpSx4/VBEnkjWNHiDxpg8v+R70rfk/Fla4OndTRQ8Bnc+MUCH7lP59zuDMKz10/
NIeWiu5T6CUVAgMBAAGjgbIwga8wDwYDVR0TAQH/BAUwAwEB/zAOBgNVHQ8BAf8E
BAMCAQYwbQYIKwYBBQUHAQwEYTBfoV2gWzBZMFcwVRYJaW1hZ2UvZ2lmMCEwHzAH
BgUrDgMCGgQUj+XTGoasjY5rw8+AatRIGCx7GS4wJRYjaHR0cDovL2xvZ28udmVy
aXNpZ24uY29tL3ZzbG9nby5naWYwHQYDVR0OBBYEFH/TZafC3ey78DAJ80M5+gKv
MzEzMA0GCSqGSIb3DQEBBQUAA4IBAQCTJEowX2LP2BqYLz3q3JktvXf2pXkiOOzE
p6B4Eq1iDkVwZMXnl2YtmAl+X6/WzChl8gGqCBpH3vn5fJJaCGkgDdk+bW48DW7Y
5gaRQBi5+MHt39tBquCWIMnNZBU4gcmU7qKEKQsTb47bDN0lAtukixlE0kF6BWlK
WE9gyn6CagsCqiUXObXbf+eEZSqVir2G3l6BFoMtEMze/aiCKm0oHw0LxOXnGiYZ
4fQRbxC1lfznQgUy286dUV4otp6F01vvpX1FQHKOtw5rDgb7MzVIcbidJ4vEZV8N
hnacRHr2lVz2XTIIM6RUthg/aFzyQkqFOFSDX9HoLPKsEdao7WNq
-----END CERTIFICATE-----

# O=Oracle Corporation, OU=Content Management Services IT
-----BEGIN CERTIFICATE-----
MIIGTzCCBTegAwIBAgIDAuO7MA0GCSqGSIb3DQEBBQUAMEAxCzAJBgNVBAYTAlVT
MRcwFQYDVQQKEw5HZW9UcnVzdCwgSW5jLjEYMBYGA1UEAxMPR2VvVHJ1c3QgU1NM
IENBMB4XDTE0MDYwMjAxMzcyMFoXDTE1MDYwNTA1MjU0M1owgdExKTAnBgNVBAUT
IFJwdzVRQjgwT1dteElXWk5iaUhXRm00djJGbkxrQVpYMQswCQYDVQQGEwJVUzET
MBEGA1UECBMKQ2FsaWZvcm5pYTEXMBUGA1UEBxMOUmVkd29vZCBTaG9yZXMxGzAZ
BgNVBAoTEk9yYWNsZSBDb3Jwb3JhdGlvbjEnMCUGA1UECxMeQ29udGVudCBNYW5h
Z2VtZW50IFNlcnZpY2VzIElUMSMwIQYDVQQDExpkb3dubG9hZC1zZWN1cmUub3Jh
Y2xlLmNvbTCCASIwDQYJKoZIhvcNAQEBBQADggEPADCCAQoCggEBAKcuWzQktPaa
uzKun4iC1x5JI4iL9wy+QIcWxQdkEzloDOiaXrL/dxJk31J2P4vFPDGWOkeMuCzY
WdTftkD+TDIuX89/dX5TTXht82rr2VJ97y5ZXfHW0rFfSb6Y3lQOG16el//APIIu
CM3B4rU7PhKHiTecg4HJ5DlvvYscp0RwXiLPEbJejKVMgV2EBZd0ipCMFAC2LYwx
r5ZUtIcc0he4GlvYVWsNEZdh9neY//HtyfBuFMsydkpLpiq7n9MEqBSJes0iIUVV
qDKCdk0ZhxmLjMui6OD8OondsWdTC3oKzXw2oDCZPsZzcRn4apHQoRY7AzENu9GC
qtC3xwaD7msCAwEAAaOCAr4wggK6MB8GA1UdIwQYMBaAFEJ5VBthzVUrPmPVPEhX
9Z/7Rc5KMA4GA1UdDwEB/wQEAwIEsDAdBgNVHSUEFjAUBggrBgEFBQcDAQYIKwYB
BQUHAwIwggE7BgNVHREEggEyMIIBLoIfZXBkLWFrYW0taW50bC1zZWN1cmUub3Jh
Y2xlLmNvbYIdZXBkLWFrYW0tdXMtc2VjdXJlLm9yYWNsZS5jb22CI2Rldi1lcGQt
YWthbS1pbnRsLXNlY3VyZS5vcmFjbGUuY29tgiFkZXYtZXBkLWFrYW0tdXMtc2Vj
dXJlLm9yYWNsZS5jb22CGmFydS1ha2FtLXNlY3VyZS5vcmFjbGUuY29tgiNmYWls
b3Zlci1hcnUtYWthbS1zZWN1cmUub3JhY2xlLmNvbYIeZGV2LWFydS1ha2FtLXNl
Y3VyZS5vcmFjbGUuY29tgidmYWlsb3Zlci1kZXYtYXJ1LWFrYW0tc2VjdXJlLm9y
YWNsZS5jb22CGmRvd25sb2FkLXNlY3VyZS5vcmFjbGUuY29tMD0GA1UdHwQ2MDQw
MqAwoC6GLGh0dHA6Ly9ndHNzbC1jcmwuZ2VvdHJ1c3QuY29tL2NybHMvZ3Rzc2wu
Y3JsMB0GA1UdDgQWBBSXz0dT9ENBUZIApd9Kz1YLGebGhTAMBgNVHRMBAf8EAjAA
MG8GCCsGAQUFBwEBBGMwYTAqBggrBgEFBQcwAYYeaHR0cDovL2d0c3NsLW9jc3Au
Z2VvdHJ1c3QuY29tMDMGCCsGAQUFBzAChidodHRwOi8vZ3Rzc2wtYWlhLmdlb3Ry
dXN0LmNvbS9ndHNzbC5jcnQwTAYDVR0gBEUwQzBBBgpghkgBhvhFAQc2MDMwMQYI
KwYBBQUHAgEWJWh0dHA6Ly93d3cuZ2VvdHJ1c3QuY29tL3Jlc291cmNlcy9jcHMw
DQYJKoZIhvcNAQEFBQADggEBADMtKZb0//q5LurSPr6er3NxMIAOyK9zZK6+Tz8j
c2bpMBFeEyRXmpDfmFR11qPx7tqOzQF/8KPi4LSWGD7EiDOD2tgeUcva6/5npNqO
pY0HTFdlWCUD3jRLqrr4mf/X5XvtfnzxCLbPCsafXGGP1Qvz9JX7SVrZqIShChMq
tWEhVOdG9vU1EGXCLQDerPgXJ7RZh0Xy/M0GEa1DaC5LxGJII4fxLD4VSZt3IOEO
EsJfaBT87379DeIlC6IbghXNKZ1R9u1wvvxMhPbJ6IttNIP3qgQcAMcU6EbtmEzR
SpTi3qtO2fxBnrxekAWyl8DDaa3QLFB4uXCZveFg1QA6UVQ=
-----END CERTIFICATE-----

# O=GeoTrust Inc., CN=GeoTrust Global CA
-----BEGIN CERTIFICATE-----
MIID2TCCAsGgAwIBAgIDAjbQMA0GCSqGSIb3DQEBBQUAMEIxCzAJBgNVBAYTAlVT
MRYwFAYDVQQKEw1HZW9UcnVzdCBJbmMuMRswGQYDVQQDExJHZW9UcnVzdCBHbG9i
YWwgQ0EwHhcNMTAwMjE5MjIzOTI2WhcNMjAwMjE4MjIzOTI2WjBAMQswCQYDVQQG
EwJVUzEXMBUGA1UEChMOR2VvVHJ1c3QsIEluYy4xGDAWBgNVBAMTD0dlb1RydXN0
IFNTTCBDQTCCASIwDQYJKoZIhvcNAQEBBQADggEPADCCAQoCggEBAJCzgMHk5Uat
cGA9uuUU3Z6KXot1WubKbUGlI+g5hSZ6p1V3mkihkn46HhrxJ6ujTDnMyz1Hr4Gu
FmpcN+9FQf37mpc8oEOdxt8XIdGKolbCA0mEEoE+yQpUYGa5jFTk+eb5lPHgX3UR
8im55IaisYmtph6DKWOy8FQchQt65+EuDa+kvc3nsVrXjAVaDktzKIt1XTTYdwvh
dGLicTBi2LyKBeUxY0pUiWozeKdOVSQdl+8a5BLGDzAYtDRN4dgjOyFbLTAZJQ50
96QhS6CkIMlszZhWwPKoXz4mdaAN+DaIiixafWcwqQ/RmXAueOFRJq9VeiS+jDkN
d53eAsMMvR8CAwEAAaOB2TCB1jAOBgNVHQ8BAf8EBAMCAQYwHQYDVR0OBBYEFEJ5
VBthzVUrPmPVPEhX9Z/7Rc5KMB8GA1UdIwQYMBaAFMB6mGiNifurBWQMEX2qfWW4
ysxOMBIGA1UdEwEB/wQIMAYBAf8CAQAwOgYDVR0fBDMwMTAvoC2gK4YpaHR0cDov
L2NybC5nZW90cnVzdC5jb20vY3Jscy9ndGdsb2JhbC5jcmwwNAYIKwYBBQUHAQEE
KDAmMCQGCCsGAQUFBzABhhhodHRwOi8vb2NzcC5nZW90cnVzdC5jb20wDQYJKoZI
hvcNAQEFBQADggEBANTvU4ToGr2hiwTAqfVfoRB4RV2yV2pOJMtlTjGXkZrUJPji
J2ZwMZzBYlQG55cdOprApClICq8kx6jEmlTBfEx4TCtoLF0XplR4TEbigMMfOHES
0tdT41SFULgCy+5jOvhWiU1Vuy7AyBh3hjELC3DwfjWDpCoTZFZnNF0WX3OsewYk
2k9QbSqr0E1TQcKOu3EDSSmGGM8hQkx0YlEVxW+o78Qn5Rsz3VqI138S0adhJR/V
4NwdzxoQ2KDLX4z6DOW/cf/lXUQdpj6HR/oaToODEj+IZpWYeZqF6wJHzSXj8gYE
TpnKXKBuervdo5AaRTPvvz7SBMS24CqFZUE+ENQ=
-----END CERTIFICATE-----

# O=GeoTrust Inc., CN=GeoTrust Global CA
-----BEGIN CERTIFICATE-----
MIIDVDCCAjygAwIBAgIDAjRWMA0GCSqGSIb3DQEBBQUAMEIxCzAJBgNVBAYT
AlVTMRYwFAYDVQQKEw1HZW9UcnVzdCBJbmMuMRswGQYDVQQDExJHZW9UcnVz
dCBHbG9iYWwgQ0EwHhcNMDIwNTIxMDQwMDAwWhcNMjIwNTIxMDQwMDAwWjBC
MQswCQYDVQQGEwJVUzEWMBQGA1UEChMNR2VvVHJ1c3QgSW5jLjEbMBkGA1UE
AxMSR2VvVHJ1c3QgR2xvYmFsIENBMIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8A
MIIBCgKCAQEA2swYYzD99BcjGlZ+W988bDjkcbd4kdS8odhM+KhDtgPpTSEH
CIjaWC9mOSm9BXiLnTjoBbdqfnGk5sRgprDvgOSJKA+eJdbtg/OtppHHmMlC
GDUUna2YRpIuT8rxh0PBFpVXLVDviS2Aelet8u5fa9IAjbkU+BQVNdnARqN7
csiRv8lVK83Qlz6cJmTM386DGXHKTubU1XupGc1V3sjs0l44U+VcT4wt/lAj
Nvxm5suOpDkZALeVAjmRCw7+OC7RHQWa9k0+bw8HHa8sHo9gOeL6NlMTOdRe
JivbPagUvTLrGAMoUgRx5aszPeE4uwc2hGKceeoWMPRfwCvocWvk+QIDAQAB
o1MwUTAPBgNVHRMBAf8EBTADAQH/MB0GA1UdDgQWBBTAephojYn7qwVkDBF9
qn1luMrMTjAfBgNVHSMEGDAWgBTAephojYn7qwVkDBF9qn1luMrMTjANBgkq
hkiG9w0BAQUFAAOCAQEANeMpauUvXVSOKVCUn5kaFOSPeCpilKInZ57Qzxpe
R+nBsqTP3UEaBU6bS+5Kb1VSsyShNwrrZHYqLizz/Tt1kL/6cdjHPTfStQWV
Yrmm3ok9Nns4d0iXrKYgjy6myQzCsplFAMfOEVEiIuCl6rYVSAlk6l5PdPcF
PseKUgzbFbS9bZvlxrFUaKnjaZC2mqUPuLk/IH2uSrW4nOQdtqvmlKXBx4Ot
2/Unhw4EbNX/3aBd7YdStysVAq45pmp06drE57xNNB6pXE0zX5IJL4hmXXeX
xx12E6nV5fEWCRE11azbJHFwLJhWC9kXtNHjUStedejV0NxPNO3CBWaAocvm
Mw==
-----END CERTIFICATE-----
