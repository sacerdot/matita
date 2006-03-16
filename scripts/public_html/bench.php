<?php require("common.php"); 
  
// syntax
//
// queries ::= query | query "###" queries
// query ::= name "@@@" sql
//
$limits = array("20","50","100");
  
$quey_all = urlencode("Whole content:@@@select * from bench order by mark desc***");
$query_fail = urlencode(
  "Number of failures@@@" .
  "select mark, count(distinct test) as fail_no from bench where result = 'fail' group by mark order by mark desc***"
  . "###" . 
  "Tests failed@@@" .
  "select distinct mark, test, result from bench where result = 'fail' order by mark desc***" 
);
$query_gc = urlencode(
  "GC usage @@@" .
  "select bench.mark, SUM(bench.time) - SUM(bench1.time) as gc_hoverhead from bench, bench as bench1 where bench.mark = bench1.mark and bench.test = bench1.test and bench.options = 'gc-on' and bench1.options = 'gc-off' and bench.compilation = bench1.compilation group by mark***"
  . "###" . 
  "GC usage (opt)@@@" .
  "select bench.mark, SUM(bench.time) - SUM(bench1.time) as gc_hoverhead from bench, bench as bench1 where bench.mark = bench1.mark and bench.test = bench1.test and bench.options = 'gc-on' and bench1.options = 'gc-off' and bench.compilation = bench1.compilation and bench.compilation = 'opt' group by mark***"
  . "###" . 
  "GC usage (byte)@@@" .
  "select bench.mark, SUM(bench.time) - SUM(bench1.time) as gc_hoverhead from bench, bench as bench1 where bench.mark = bench1.mark and bench.test = bench1.test and bench.options = 'gc-on' and bench1.options = 'gc-off' and bench.compilation = bench1.compilation and bench.compilation = 'byte' group by mark***"
  
);
$query_auto = urlencode(
  "Auto (with GC)@@@select mark, SUM(bench.time) as time from bench where test='auto.ma' and options = 'gc-on' group by mark order by mark desc***"
  . "###" . 
  "Auto (without GC)@@@select mark, SUM(bench.time) as time from bench where test='auto.ma' and options = 'gc-off' group by mark order by mark desc***"
    . "###" . 
   "GC overhead@@@select bench.mark, SUM(bench.time) - SUM(bench1.time) as gc_hoverhead from bench, bench as bench1 where bench.mark = bench1.mark and bench.test = bench1.test and bench.options = 'gc-on' and bench1.options = 'gc-off' and bench.compilation = bench1.compilation and bench.test = 'auto.ma' group by mark"
);

$query_csc = urlencode("Performances (byte and GC) per mark@@@select bench.mark ,bench_svn.revision as revision, SUM(bench.time) as sum_time, SUM(bench.timeuser) as sum_timeuser from bench, bench_svn where bench.options = 'gc-on' and bench.compilation = 'byte' and bench_svn.mark = bench.mark group by bench.mark order by bench.mark desc"
);

$query_csc_opt = urlencode("Performances (opt and GC) per mark@@@select bench.mark,bench_svn.revision as revision, SUM(bench.time) as sum_time, SUM(bench.timeuser) as sum_timeuser from bench, bench_svn where bench.options = 'gc-on' and bench.compilation = 'opt' and bench_svn.mark = bench.mark group by bench.mark order by bench.mark desc"
);

$query_total = urlencode(
  
"Max N@@@select COUNT(DISTINCT test) as MAX from bench group by mark order by MAX desc LIMIT 0,1;"
  . "###" .
  "Number of compiled tests@@@select mark, COUNT(DISTINCT test) as N from bench group by mark order by mark desc***"
);

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

?>

<html>
  <head>
  <link type="text/css" rel="stylesheet" href="style.css"/>
  </head>
  <body>
    <h1>QUERY the benchmark system</h1>
    <h2>Common Queries</h2>
    <p>
      <ul>
      <? links_of("Broken tests",$query_fail,$limits) ?>
      <? links_of("Garbage collector killer",$query_gc,$limits) ?>
      <? links_of("Auto performances",$query_auto,$limits) ?>
      <? links_of("Global performances (bytecode)",$query_csc,$limits) ?>
      <? links_of("Global performances (nativecode)",$query_csc_opt,$limits) ?>
      <? links_of("Number of compiled tests",$query_total,$limits) ?>
      <? links_of("All table contents",$quey_all,$limits) ?>
      </ul>
    </p>
    <h2>Custom Query</h2>
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
          <?query("select distinct test from bench;","array_to_combo");?>
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
</body>
</html>
