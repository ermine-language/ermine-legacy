name := "ermine-legacy"

organization := "com.clarifi"

version := "0.1"

scalaVersion := "2.10.2"

crossScalaVersions := Seq("2.10.2")

description := "Legacy Ermine Type Checker and Interpreter in Scala."

licenses += ("BSD Simplified", url("https://github.com/ermine-language/ermine-legacy/blob/master/LICENSE"))

bintray.Keys.bintrayOrganization in bintray.Keys.bintray := Some("ermine")

seq(bintraySettings:_*)

publishMavenStyle := true

scalacOptions ++=
  Seq("-encoding", "UTF-8", "-Yrecursion", "50", "-deprecation",
      "-unchecked", "-Xlint", "-feature",
      "-language:implicitConversions", "-language:higherKinds",
      "-language:existentials", "-language:postfixOps")

javacOptions ++=
  Seq("-Xlint:cast", "-Xlint:deprecation", "-Xlint:empty",
      "-Xlint:finally", "-Xlint:fallthrough", "-Xlint:overrides")

parallelExecution := true

javacOptions += "-Xlint"

scalacOptions ~= (so => (so filterNot Set("-unchecked", "-Xlint"))
                    ++ Seq("-Ywarn-nullary-override", "-Ywarn-inaccessible"))

// We're still using scala-iterv; we know, so stop telling us.
logManager in Compile ~= {coreLogMgr =>
  filterLogs(coreLogMgr){coreLog =>
    val suppWarnTails = Seq("in package scalaz is deprecated: Scalaz 6 compatibility. Migrate to scalaz.iteratee.",
                            // -unchecked always on in 2.10.2 compiler I think
                            "is unchecked since it is eliminated by erasure")
    val suppress = new java.util.concurrent.atomic.AtomicInteger(0)
    def zero(n:Int) = suppress.compareAndSet(n, 0)
    (level, message) => {
      suppress.decrementAndGet() match {
        case n if suppWarnTails exists message.endsWith =>
          suppress.compareAndSet(n, 2)
        case 1 if level == Level.Warn => ()
        case 0 if level == Level.Warn && (message endsWith "^") => ()
        case n if coreLog atLevel level =>
          zero(n)
          coreLog.log(level, message)
        case n => zero(n)
      }
    }
  }
}

libraryDependencies ++= Seq(
  "org.scalaz" %% "scalaz-core" % "7.0.2",
  "org.scalaz" %% "scalaz-concurrent" % "7.0.2",
  "org.scalaz" %% "scalaz-effect" % "7.0.2",
  "org.scalaz" %% "scalaz-iterv" % "7.0.2",
  "org.scalaz" %% "scalaz-scalacheck-binding" % "7.0.2" % "test",
  "machines"   %% "machines" % "1.0",
  //"org.scala-lang" % "jline" % "2.10.2",
  "jline" % "jline" % "0.9.91",
  "log4j" % "log4j" % "1.2.14",
  "net.sourceforge.jtds" % "jtds" % "1.3.1",
  "org.xerial" % "sqlite-jdbc" % "3.7.2",
  "mysql" % "mysql-connector-java" % "5.1.6",
  "postgresql" % "postgresql" % "9.1-901-1.jdbc4",
  "org.scalacheck" %% "scalacheck" % "1.10.0" % "test"
)
