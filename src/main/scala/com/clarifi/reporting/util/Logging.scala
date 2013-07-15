package com.clarifi.reporting.util

import scala.util.control.NonFatal

object Logging {
  import org.apache.log4j.{Logger,PropertyConfigurator}

  def initializeLogging: Unit = {
    val filename = "res/conf/log4j.prp"
    if( new java.io.File( filename ).isFile ) {
      try
      {
        PropertyConfigurator.configure( filename );
      }
      catch { case NonFatal(e) =>
        /**
         * One of the few places to print an exception to STDERR because
         * log4j is not available.
         */
        System.err.println( "Failed to configure log4j" );
        e.printStackTrace();
      }
    }
    else {
      System.out.println( "logging config not found (" + filename + "), using defaults" );
      val props = new java.util.Properties();
      val logLevel = "WARN"
      props.put( "log4j.rootCategory", logLevel + ", stdout" )
      props.put( "log4j.appender.stdout", "org.apache.log4j.ConsoleAppender" )
      props.put( "log4j.appender.stdout.layout", "org.apache.log4j.PatternLayout" )
      props.put( "log4j.appender.stdout.layout.ConversionPattern",
          "[%d{dd MMM yyyy HH:mm:ss,SSS}] %-6p %-25c{1} | %m%n" )
      PropertyConfigurator.configure( props )         
    }
  }
}
