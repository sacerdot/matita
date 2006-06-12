<?xml version="1.0" encoding="utf-8"?>
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="1.0">

  <xsl:import href="http://db2latex.sourceforge.net/xsl/docbook.xsl"/>
  <xsl:output method="text" encoding="utf-8" indent="yes"/>

  <xsl:param name="admon.graphics.path">/usr/share/xml/docbook/stylesheet/db2latex/latex/figures</xsl:param>

  <xsl:param name="latex.inputenc">utf8x</xsl:param>
  <xsl:param name="latex.book.preamble.post">\usepackage{txfonts}
\SetUnicodeOption{mathletters} % prefer math-mode letters
</xsl:param>
  <xsl:param name="ulink.show">0</xsl:param>

  <!-- proper alignment of tables used for grammars -->

  <xsl:template match="tgroup[../@role='grammar']">
    <xsl:text>\begin{tabular}{rcll}
</xsl:text>
    <xsl:apply-templates />
    <xsl:text>\end{tabular}
</xsl:text>
  </xsl:template>

  <xsl:template match="variablelist/title">
    <xsl:text>\paragraph*{</xsl:text>
    <xsl:apply-templates />
    <xsl:text>} </xsl:text>
  </xsl:template>

</xsl:stylesheet>
