<?xml version="1.0" encoding="utf-8"?>
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="1.0">

  <xsl:import href="http://db2latex.sourceforge.net/xsl/docbook.xsl"/>
  <xsl:output method="text" encoding="utf-8" indent="yes"/>

  <xsl:param name="admon.graphics.path">/usr/share/xml/docbook/stylesheet/db2latex/latex/figures</xsl:param>

  <xsl:param name="latex.inputenc">utf8x</xsl:param>
  <xsl:param name="latex.book.preamble.post">\usepackage{txfonts}
\SetUnicodeOption{mathletters} % prefer math-mode letters
</xsl:param>

</xsl:stylesheet>
