<xsl:stylesheet version="1.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

  <xsl:output
    method="xml"
    indent="yes"
    omit-xml-declaration="yes"
    />

  <xsl:param name="declarative" value=""/>

  <xsl:template match="/">
    <table frame="topbot" rowsep="0" colsep="0" role="grammar">
      <title>tactics</title>
      <tgroup cols="3">
      <tbody>
       <xsl:apply-templates select="//chapter[@id=concat('sec_',$declarative,'tactics')]//varlistentry[@role='tactic.synopsis']">
	 <xsl:sort select="ancestor::sect1/title" />
       </xsl:apply-templates>
      </tbody>
     </tgroup>
    </table>
  </xsl:template>

  <xsl:template match="varlistentry">

    <xsl:variable name="tactic">
      <xsl:value-of select="ancestor::sect1/title" />
    </xsl:variable>

    <row>
      <entry>
       <xsl:choose>
        <xsl:when test="position()=1">
         <xsl:attribute name="id">grammar.<xsl:value-of select="$declarative"/>tactic</xsl:attribute>
         <xsl:text disable-output-escaping='yes'>&amp;tactic;</xsl:text>
        </xsl:when>
       </xsl:choose>
      </entry>
      <entry>
       <xsl:choose>
        <xsl:when test="position()=1">
         <xsl:text>::=</xsl:text>
        </xsl:when>
        <xsl:otherwise>
         <xsl:text>|</xsl:text>
        </xsl:otherwise>
       </xsl:choose>
      </entry>
      <entry>
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
      </entry>
    </row>

  </xsl:template>

</xsl:stylesheet>
