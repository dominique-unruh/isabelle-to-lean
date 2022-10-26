package isabelle2scala2

object Utils {
  def runAsDaemon(task: => Any): Unit = {
    val thread = new Thread({ () => task } : Runnable)
    thread.setDaemon(true)
    thread.start()
  }
}
