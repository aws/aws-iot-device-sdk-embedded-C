#ifndef HTTP_CONFIG_H__
#define HTTP_CONFIG_H__

#include "logging_levels.h"

#define LIBRARY_LOG_NAME     "HTTP"
#define LIBRARY_LOG_LEVEL    LOG_DEBUG

/**** NOTE: Include logging stack ONLY after the library name and log level configuration. ******/
#include "logging_stack.h"

#endif /* ifndef HTTP_CONFIG_H__ */
