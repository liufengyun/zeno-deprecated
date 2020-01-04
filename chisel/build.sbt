scalaVersion := "2.12.6"

scalacOptions := Seq("-Xsource:2.11")

resolvers ++= Seq(
  Resolver.sonatypeRepo("snapshots"),
  Resolver.sonatypeRepo("releases")
)

test := {
  (runMain in Compile).toTask(" leros.Test").value
}

libraryDependencies += "edu.berkeley.cs" %% "chisel3" % "3.1.7"
libraryDependencies += "edu.berkeley.cs" %% "chisel-iotesters" % "1.2.8"

