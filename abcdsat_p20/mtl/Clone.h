#ifndef abcdSAT_Clone_h
#define abcdSAT_Clone_h


namespace abcdSAT {

    class Clone {
        public:
          virtual Clone* clone() const = 0;
    };
};

#endif
