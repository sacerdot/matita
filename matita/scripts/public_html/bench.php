<?php require("common.php"); 
  
// syntax
//
// queries ::= query | query "###" queries
// query ::= name "@@@" sql
//
$limits = array("20","50","100");

$query_last_mark = "select mark from bench order by mark desc limit 1;";
$last_mark = "";
function set_last_mark($a) {
 global $last_mark;
 foreach ($a as $k => $v) {
   $last_mark = $v;
 }
}
query($query_last_mark,"set_last_mark");

$query_last_svn_mark = "select revision from bench_svn where mark='$last_mark';";
$last_svn_mark = "";
function set_last_svn_mark($a) {
 global $last_svn_mark;
 foreach ($a as $k => $v) {
   $last_svn_mark = trim($v);
 }
}
query($query_last_svn_mark,"set_last_svn_mark");

$query_before_last_mark = "select mark from bench where mark <> '$last_mark' order by mark desc limit 1;";
$before_last_mark = "";
function set_before_last_mark($a) {
 global $before_last_mark;
 foreach ($a as $k => $v) {
   $before_last_mark = $v;
 }
}
query($query_before_last_mark,"set_before_last_mark");

$query_before_last_svn_mark = "select revision from bench_svn where mark='$before_last_mark';";
$before_last_svn_mark = "";
function set_before_last_svn_mark($a) {
 global $before_last_svn_mark;
 foreach ($a as $k => $v) {
   $before_last_svn_mark = trim($v);
 }
}
query($query_before_last_svn_mark,"set_before_last_svn_mark");

  
$quey_all = urlencode("
Whole content:
@@@
select * from bench order by mark desc***");

$query_time_diff = urlencode("
Time diff:
@@@
select 
  b1.test as test, b1.timeuser as oldtime, b2.timeuser as newtime, b1.compilation as comp, b1.options as opts,
  (b2.timeuser - b1.timeuser) as diff
from 
  bench as b1, bench as b2 
where 
  b1.test = b2.test and 
  b1.options = b2.options and
  b1.compilation = b2.compilation and 
  b1.result = b2.result and 
  b1.mark = '$before_last_mark' and b2.mark= '$last_mark' and
  ABS(b2.timeuser - b1.timeuser) > 100
order by diff desc***");

$query_result_diff = urlencode("
Result diff:
@@@
select 
  b1.test as test, b1.result as oldresult, b2.result as newresult, b1.timeuser as oldtime, b2.timeuser as newtime, b1.compilation as comp, b1.options as opts,
  (b2.timeuser - b1.timeuser) as diff
from 
  bench as b1, bench as b2 
where 
  b1.test = b2.test and 
  b1.options = b2.options and
  b1.compilation = b2.compilation and 
  b1.result <> b2.result and 
  b1.mark = '$before_last_mark' and b2.mark= '$last_mark'
order by test desc***");

$query_fail = urlencode("
Number of failures
@@@
select 
  mark, count(distinct test) as fail_no 
from bench 
where result = 'fail' group by mark order by mark desc***
###
Tests failed
@@@
select distinct mark, test, result 
from bench 
where result = 'fail' order by mark desc***");

$query_gc = urlencode("
GC usage 
@@@
select 
  bench.mark, SUM(bench.time) - SUM(bench1.time) as gc_hoverhead 
from bench, bench as bench1 
where 
  bench.mark = bench1.mark and 
  bench.test = bench1.test and 
  bench.options = 'gc-on' and
  bench1.options = 'gc-off' and 
  bench.compilation = bench1.compilation 
group by mark***
###
GC usage (opt)
@@@
select 
  bench.mark, SUM(bench.time) - SUM(bench1.time) as gc_hoverhead 
from bench, bench as bench1
where 
  bench.mark = bench1.mark and 
  bench.test = bench1.test and 
  bench.options = 'gc-on' and 
  bench1.options = 'gc-off' and 
  bench.compilation = bench1.compilation and 
  bench.compilation = 'opt' 
group by mark***");

$query_auto = urlencode("
Auto (with GC)
@@@
select 
  mark, SUM(bench.time) as time 
from 
  bench 
where 
  test='auto.ma' and options = 'gc-on' 
group by mark 
order by mark desc***
### 
Auto (without GC)
@@@
select 
  mark, SUM(bench.time) as time 
from 
  bench 
where 
  test='auto.ma' and options = 'gc-off' 
group by mark 
order by mark desc
***
### 
GC overhead
@@@
select 
  bench.mark, SUM(bench.time) - SUM(bench1.time) as gc_hoverhead 
from 
  bench, bench as bench1 
where 
  bench.mark = bench1.mark and 
  bench.test = bench1.test and 
  bench.options = 'gc-on' and 
  bench1.options = 'gc-off' and 
  bench.compilation = bench1.compilation and 
  bench.test = 'auto.ma' 
group by mark
***");

$query_csc = urlencode("
Performances per mark
@@@
select 
  bench_times_opt.mark as mark,
  bench_svn.revision,
  bench_times_opt.time     as time_opt,
  bench_times_opt.timeuser as timeuser_opt,
  bench_times_opt.tests as tests_opt,
  bench_fails_opt.count as fail_opt
from 
  bench_svn, 
  (select 
    b1.mark as mark, SUM(b1.time) as time, 
    SUM(b1.timeuser) as timeuser,COUNT(DISTINCT b1.test) as tests
   from bench as b1
   where 
     b1.options = 'gc-on' and 
     b1.compilation = 'opt' 
     group by b1.mark) as bench_times_opt,
  (select
    b1.mark as mark,
    SUM(if(b1.result='fail' and b1.compilation='opt' and b1.options='gc-on',1,0))
    as count
   from bench as b1
   group by b1.mark) as bench_fails_opt
where 
  bench_times_opt.mark = bench_fails_opt.mark and 
  bench_svn.mark = bench_times_opt.mark 
  order by bench_svn.mark desc
***");

$query_total = urlencode("
Max N
@@@
select 
  COUNT(DISTINCT test) as MAX 
from 
  bench 
group by mark 
order by MAX desc 
LIMIT 0,1;
###
Number of compiled tests
@@@
select 
  mark, 
  COUNT(DISTINCT test) as N 
from 
  bench 
group by mark 
order by mark desc
***");

function minus1_to_all($s){
  if ($s == "-1") 
    return "all";
  else 
    return $s;
}

function links_of($name,$q,$limits){
  echo "<li>$name :&nbsp;&nbsp;&nbsp;";
  if (strpos($q, urlencode("***")) === false) {
    echo "<a href=\"showquery.php?query=$q;\">all</a>";
  } else {
    foreach($limits as $l) {
      $q1 = str_replace(urlencode("***"), " LIMIT 0,$l", $q);
      echo "<a href=\"showquery.php?query=$q1;\">" . 
            minus1_to_all($l) . "</a>&nbsp;&nbsp;";
    }
      $q1 = str_replace(urlencode("***"), " ", $q);
      echo "<a href=\"showquery.php?query=$q1;\">" . 
            minus1_to_all("-1") . "</a>&nbsp;&nbsp;";
  }
  echo "</li>";
}

function last_commits() {
 global $last_svn_mark;
 global $before_last_svn_mark;
 $query = "svn log -r$last_svn_mark:$before_last_svn_mark -v svn://mowgli.cs.unibo.it/trunk/helm/software";
 echo $query;
 exec($query,$res);
 echo "<pre>";
 foreach ($res as $k => $v) { echo "$v\n"; }
 echo "</pre>";
}

?>

<html>
  <head>
  <link type="text/css" rel="stylesheet" href="style.css"/>
  </head>
  <body>
    <h1>QUERY the benchmark system</h1>
    <h2>Last Commits</h2>
    <? last_commits() ?>
    <h2>Common Queries</h2>
    <p>
      <ul>
      <? links_of("Broken tests",$query_fail,$limits) ?>
      <? links_of("Time diff",$query_time_diff,$limits) ?>
      <? links_of("Result diff",$query_result_diff,$limits) ?>
      <? links_of("Garbage collector killer",$query_gc,$limits) ?>
      <? links_of("Auto performances",$query_auto,$limits) ?>
      <? links_of("Global performances",$query_csc,$limits) ?>
      <? links_of("Number of compiled tests",$query_total,$limits) ?>
      <? links_of("All table contents",$quey_all,$limits) ?>
      </ul>
    </p>
    <h2>Custom Query - Simple Interface</h2>
    <form action="composequery.php" method="get">
    <table>
  <tr>
    <td>Marks:</td>
    <td> 
      <select name="mark">";
        <option value="--">--</option>";
        <?query("select distinct mark from bench order by mark desc;",
            "array_to_combo");?>
      </select>      
    </td>
  </tr>
  <tr>
    <td>Compilations:</td>
    <td> 
      <select name="compilation">";
        <option value="--">--</option>";
          <?query("select distinct compilation from bench;","array_to_combo");?>
      </select>      
    </td>
  </tr>
  <tr>
    <td>Options:</td>
    <td>  
      <select name="options">";
        <option value="--">--</option>";
          <?query("select distinct options from bench;","array_to_combo");?>
      </select>      
    </td>
  </tr>
  <tr>
    <td>Tests:</td>
    <td>    
      <select name="test">";
        <option value="--">--</option>";
          <?query("select distinct test from bench order by test;","array_to_combo");?>
      </select>      
    </td>
  </tr>
  <tr>
    <td>Test results:</td>
    <td>
      <select name="result">";
        <option value="--">--</option>";
          <?query("select distinct result from bench;","array_to_combo"); ?>
      </select>      
    </td>
  </tr>
  <tr>
    <td>Group By: </td>
    <td>
      <select name="groupby">";
        <option value="--">--</option>";
        <? array_to_combo(array("mark"));array_to_combo(array("options")); ?>
      </select>      
    </td>
  </tr>
  <tr>
    <td>Limit: </td>
    <td>
      <select name="limit">";
        <option value="--">--</option>";
      <? foreach(array($limits) as $l) {array_to_combo($l);} ?>
      </select>      
    </td>
  </tr>
  <tr>
    <td><input type="submit" value="Submit" class="button" /></td>
  </tr>
 </table>
</form>
<h2>Custom Query - raw SQL</h2>
<form action="showquery.php" method="get">
<table>
<tr><td>'bench' table description:</td></tr>
</tr>
<? query("describe bench","printer"); $i=0; ?>
</tr>
<tr><td></td></tr>
<tr><td></td></tr>
<tr><td>'bench_svn' table description:</td></tr>
</tr>
<? query("describe bench_svn","printer"); $i=0; ?>
</tr>
<tr><td></td></tr>
<tr><td colspan="7">
SQL (only one query, ';' if present must terminate the query, no characters allowed after it):</td></tr>
<tr><td colspan="7">
<textarea rows="10" cols="120" name="query"/>
select 
  b1.test as test, b1.timeuser as oldtime, b2.timeuser as newtime, b1.compilation as comp, b1.options as opts,
  (b2.timeuser - b1.timeuser) as diff
from 
  bench as b1, bench as b2 
where 
  b1.test = b2.test and 
  b1.options = b2.options and
  b1.compilation = b2.compilation and 
  b1.result = b2.result and 
  b1.mark = '<?php echo $before_last_mark ?>' and b2.mark= '<?php echo $last_mark ?>' and
  ABS(b2.timeuser - b1.timeuser) &gt; 100
order by diff desc;
</textarea>
</td>
</tr>
<tr><td>
<input type="submit" value="Submit" class="button" /></td>
</tr>
</table>
</form>

</body>
</html>
