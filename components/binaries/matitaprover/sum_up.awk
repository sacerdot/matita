function process(name,calls,time) {
  if (! name in data_calls ) {
    data_calls[name] = 0;  
    data_time[name] = 0;  
  }
  data_calls[name] = data_calls[name] + calls;
  data_time[name] = data_time[name] + time;
}
# ---------------------------------------------- 
($1 == "!!") { process($2,$3,$4); }
END {
  printf "%40s %10s %s\n", "name", "calls", "time";
  for (i in data_time) {
    printf "%40s %10d %03.3f %.8f\n", i, data_calls[i], data_time[i],  data_time[i]/ data_calls[i];
  }  
}
