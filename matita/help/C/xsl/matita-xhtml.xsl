<?xml version="1.0" encoding="utf-8"?>

<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="1.0">

  <xsl:import href="http://docbook.sourceforge.net/release/xsl/current/xhtml/chunk.xsl"/>
  <xsl:output method="xml" encoding="utf-8" indent="yes"/>

  <xsl:param name="use.id.as.filename" select="1" />
  <xsl:param name="html.stylesheet">docbook.css</xsl:param>
  <xsl:param name="table.borders.with.css" select="1" />
  <!--
  <xsl:param name="header.rule" select="0" />
  <xsl:param name="footer.rule" select="0" />
  -->

  <!-- more quiet output of author information -->

  <xsl:template match="authorgroup" mode="titlepage.mode">
    <ul class="authorgroup">
      <xsl:apply-templates mode="matita.manual.mode" />
    </ul>
  </xsl:template>
  <xsl:template match="author" mode="matita.manual.mode">
    <li class="author">
      <xsl:value-of select="firstname" />
      <xsl:text> </xsl:text>
      <xsl:value-of select="surname" />
      <xsl:text> &lt;</xsl:text>
      <xsl:element name="a">
	<xsl:attribute name="href">
	  <xsl:text>mailto:</xsl:text>
	  <xsl:value-of select="affiliation/address/email" />
	</xsl:attribute>
	<xsl:value-of select="affiliation/address/email" />
      </xsl:element>
      <xsl:text>&gt;</xsl:text>
    </li>
  </xsl:template>

  <!-- only print the latest revision instead of all of them -->
  <!-- XXX ZACK: right now it just assumes that only one revision does exist -->

  <xsl:template match="revhistory" mode="titlepage.mode">
    <div class="revhistory">
      <xsl:apply-templates mode="matita.manual.mode" />
    </div>
  </xsl:template>
  <xsl:template match="revision" mode="matita.manual.mode">
    <span class="revision">
      <xsl:text>Revision: </xsl:text>
      <span class="revnumber">
	<xsl:value-of select="revnumber" />
      </span>
      <xsl:text>, </xsl:text>
      <span class="date">
	<xsl:value-of select="date" />
      </span>
    </span>
  </xsl:template>

  <!-- Matita logo on the top left corner -->

  <xsl:template name="user.header.navigation">
	  <a href="../../../">
      <div class="matita_logo">
	<img src="figures/matita.png" alt="Tiny Matita logo" />
	<span>Matita Home</span>
      </div>
    </a>
  </xsl:template>

</xsl:stylesheet>

