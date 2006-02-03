<?php

function query($q) {
  $db = mysql_pconnect("localhost","helm");
  mysql_select_db("matita");
  if (preg_match("/TIME_TO_SEC/",$q)) {
    $group_by = true;
    $q = preg_replace("/group by bench.mark/","",$q);
    $q = preg_replace("/SEC_TO_TIME\(SUM\(TIME_TO_SEC\(([^)]+)\)\)\)/","$1",$q);
  }
  $rc = mysql_query($q,$db);
  if(!$rc) {
    die("Query failed: " . mysql_error());
  }
  $result = array();
  while( $row = mysql_fetch_array($rc, MYSQL_ASSOC)){
    $result[] = $row;
  }
  mysql_free_result($rc);
  mysql_close($db);
  if ($group_by){
    return group_array_by_mark($result);
  } else {
    return $result;
  }
}

function time_2_cents($t) {
  $matches = array();
  $rex = "/^(\d+)m(\d\d?)\.(\d{2})s$/";
  $m = preg_match($rex,$t,$matches);
  if ( $m == 0 ) exit(1);
  $t_minutes = $matches[1];
  $t_secs = $matches[2];
  $t_cents = $matches[3];
  return ((int) $t_cents) + ((int) $t_secs) * 100 + ((int)$t_minutes) * 6000 ;
}

function sum_time($t1, $t2) {
  $matches1 = array();
  $matches2 = array();
  $rex = "/^(\d+)m(\d\d?)\.(\d{2})s$/";
  $m1 = preg_match($rex,$t1,$matches1);
  $m2 = preg_match($rex,$t2,$matches2);
  if ($m1 != 0 && $m2 != 0) {
    $t1_minutes = $matches1[1];
    $t2_minutes = $matches2[1];
    $t1_secs = $matches1[2];
    $t2_secs = $matches2[2];
    $t1_cents = $matches1[3];
    $t2_cents = $matches2[3];
    $time1 = ((int) $t1_cents) + ((int) $t1_secs) * 100 + ((int)$t1_minutes) * 6000 ;
    $time2 = ((int) $t2_cents) + ((int) $t2_secs) * 100 + ((int)$t2_minutes) * 6000 ;
    $sum = $time1 + $time2;
    $min = $sum / 6000;
    $sec = ($sum % 6000) / 100;
    $cent = ($sum % 6000) % 100;
    return sprintf("%dm%02d.%02ds",$min,$sec,$cent);
  } else {
    return $t1;
  }
}

function group_array_by_mark($a) {
  $rc = array();
  foreach ($a as $x) {
    if ($rc[$x['mark']] == NULL) {
      $rc[$x['mark']] = $x;
    } else {
      foreach ($rc[$x['mark']] as $k => $v) {
        $rc[$x['mark']][$k] = sum_time($v, $x[$k]);
      }
    }
  }
  return array_values($rc);
}
  
function array_to_combo($l,$a) {
  echo "<select name=\"$l\">";
  echo "<option value=\"--\">--</option>";
  foreach ($a as $k => $v) {
    foreach( array_keys($v) as $k1 => $i) {
      echo "<option value=\"{$v[$i]}\">{$v[$i]}</option>";
    }
  }
  echo "</select>";
}

?>
