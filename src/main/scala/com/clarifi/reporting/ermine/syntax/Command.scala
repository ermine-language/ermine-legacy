package com.clarifi.reporting.ermine.syntax
import com.clarifi.reporting.ermine.{ Term }

sealed trait Command
case class ImportExportCommand(s: ImportExportStatement) extends Command
case class ModuleCommand(s: Module) extends Command
case class ExpressionCommand(s: Term) extends Command
case object EmptyCommand extends Command
