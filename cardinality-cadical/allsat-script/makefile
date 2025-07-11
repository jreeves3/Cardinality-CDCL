# Define the compiler
CXX = g++

# Define the compiler flags
CXXFLAGS = -std=c++11 -I../src/

# Define the linker flags
LDFLAGS = -L../build/ -lcadical

# Define the target executable
TARGET = allsat

# Define the source files
SRCS = allsat.cpp

# Define the object files
OBJS = $(SRCS:.cpp=.o)

# Default target
all: $(TARGET)

# Rule to build the target executable
$(TARGET): $(OBJS)
		$(CXX) $(OBJS) -o $(TARGET) $(LDFLAGS)

# Rule to build the object files
%.o: %.cpp
		$(CXX) $(CXXFLAGS) -c $< -o $@

# Clean up build files
clean:
		rm -f $(OBJS) $(TARGET)