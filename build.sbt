name := "ermine"

organization := "com.clarifi"

version := "0.1"

scalaVersion := "2.10.2"

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
  //"org.scala-lang" % "jline" % "2.10.2",
  "jline" % "jline" % "0.9.91",
  "log4j" % "log4j" % "1.2.14",
  "org.scalaz" %% "scalaz-scalacheck-binding" % "7.0.2" % "test",
  "org.scalacheck" %% "scalacheck" % "1.10.0" % "test"
)

