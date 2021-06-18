PKG = Gym
include $(LEAN4_S1_MK)
all: gym

GymEXE=lean-gym
LEAN4_PATH=$(LEAN4_S1_LIB)

gym: $(BIN_OUT)/test
	cp $(BIN_OUT)/test $(GymEXE)

$(BIN_OUT)/test: $(LIB_OUT)/libGym.a $(CPP_OBJS) | $(BIN_OUT)
	c++ -rdynamic -o $@ $^ `leanc --print-ldflags`
