package com.clarifi.reporting

import java.sql.Connection

package object backends {
  type DB[+A] = Connection => A
}

