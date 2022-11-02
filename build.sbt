ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.2.0"

lazy val root = (project in file("."))
  .settings(
    name := "isabelle-to-lean",

    libraryDependencies += ("de.unruh" %% "scala-isabelle" % "master-SNAPSHOT").cross(CrossVersion.for3Use2_13),
    libraryDependencies += "org.apache.commons" % "commons-text" % "1.10.0",
    libraryDependencies += "org.scalaz" %% "scalaz" % "7.3.6",
    Compile / resourceDirectory := baseDirectory.value / "src" / "lean",
)
