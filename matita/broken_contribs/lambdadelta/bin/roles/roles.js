function filter(req, ptr) {
  var query = document.getElementById('f.'+ptr).value;
  var anchor = document.getElementById('s.'+ptr);
  var cl = document.getElementsByName(ptr);
  var s = "";
  for (i=0;i < cl.length; i++) {
    if (cl[i].getAttribute('key').search(query) >= 0) {
      cl[i].classList.remove('hidden');
      s = s + cl[i].getAttribute('ord') + ',';
    } else {
      cl[i].classList.add('hidden');
    }
  };
  anchor.setAttribute('href', req + '.' + s);
}
