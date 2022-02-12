set (KmeldSourceCodes
	Kmeld.h
	Kmeld.cc
	CriticalFunc.h
	CriticalFunc.cc
)

# Build libraries.
add_library (KmeldObj OBJECT ${KmeldSourceCodes})
add_library (Kmeld SHARED $<TARGET_OBJECTS:KmeldObj>)
add_library (KmeldStatic STATIC $<TARGET_OBJECTS:KmeldObj>)

# Build executable unisan.
set (EXECUTABLE_OUTPUT_PATH ${UNISAN_BINARY_DIR})
link_directories (${UNISAN_BINARY_DIR}/lib)
add_executable(k-meld ${KmeldSourceCodes})
target_link_libraries(k-meld
  LLVMAsmParser
  LLVMSupport
  LLVMCore
  LLVMAnalysis
  LLVMIRReader
  KmeldStatic
  )
