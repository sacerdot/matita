<xsl:stylesheet version="1.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

  <xsl:output
    method="xml"
    indent="yes"
    omit-xml-declaration="yes"
    />

  <xsl:template match="/">
    <itemizedlist>
      <xsl:apply-templates select="//varlistentry[@role='tactic.synopsis']">
	<xsl:sort select="ancestor::sect1/title" />
      </xsl:apply-templates>
    </itemizedlist>
  </xsl:template>

  <xsl:template match="varlistentry">

    <xsl:variable name="tactic">
      <xsl:value-of select="ancestor::sect1/title" />
    </xsl:variable>

    <listitem>
      <para>
	<xsl:for-each select="listitem/para/* | listitem/para/child::text()">
	  <xsl:choose>

	    <xsl:when test="string(.) = $tactic">
	      <xsl:element name="link">
		<xsl:attribute name="linkend">
		  <xsl:text>tac_</xsl:text>
		  <xsl:value-of select="$tactic" />
		</xsl:attribute>
		<xsl:copy-of select="." />
	      </xsl:element>
	    </xsl:when>

	    <xsl:otherwise>
	      <xsl:copy-of select="." />
	    </xsl:otherwise>

	  </xsl:choose>
	</xsl:for-each>
      </para>
    </listitem>

  </xsl:template>

</xsl:stylesheet>
