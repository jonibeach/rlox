use codecrafters_interpreter::{
    eval::{ErrorKind, Executor},
    lexer::{Keyword, Lexer, Token},
    parser::Parser,
};

macro_rules! assert_program_stdout {
    ($program: literal, $($stdout_line: expr),*) => {
        let mut lexer = Lexer::new();
        let src = $program;

        lexer.lex(src);

        assert_eq!(lexer.errors(), [].as_slice());

        let mut parser = Parser::new(lexer.tokens());
        let program = parser.parse().unwrap();
        let mut stdout: Vec<u8> = Vec::new();
        let executor = Executor::new(program.decls(), &mut stdout);
        executor.run().unwrap();

        let stdout = String::from_utf8(stdout).unwrap();
        let mut lines = stdout.lines();

        $(
         assert_eq!(lines.next().unwrap().trim(), $stdout_line);
        )*

        assert!(lines.next().is_none());
    };
}

#[test]
fn bool() {
    let mut lexer = Lexer::new();
    let src = "true;";
    lexer.lex(src);

    assert_eq!(
        lexer.without_symbols(),
        vec![Token::Keyword(Keyword::True), Token::Semicolon]
    );

    let mut parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();

    assert_eq!(
        format!("{}", program.decls().iter().next().unwrap()),
        "true"
    );
    let executor = Executor::with_stdout(program.decls());
    let res = executor.eval().unwrap();

    assert_eq!(res, "true")
}

#[test]
fn nil() {
    let mut lexer = Lexer::new();
    let src = "nil;";
    lexer.lex(src);

    let mut parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let executor = Executor::with_stdout(program.decls());
    let res = executor.eval().unwrap();

    assert_eq!(res, "nil")
}

#[test]
fn unarys() {
    let mut lexer = Lexer::new();
    let src = "(!nil) == true;";
    lexer.lex(src);

    let mut parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let executor = Executor::with_stdout(program.decls());
    let res = executor.eval().unwrap();

    assert_eq!(res, "true")
}

#[test]
fn numbers() {
    let mut lexer = Lexer::new();
    let src = "1+2*45;";
    lexer.lex(src);

    let mut parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let executor = Executor::with_stdout(program.decls());
    let res = executor.eval().unwrap();

    assert_eq!(res, "91")
}

#[test]
fn neg_number() {
    let mut lexer = Lexer::new();
    let src = "-2;";
    lexer.lex(src);

    let mut parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let executor = Executor::with_stdout(program.decls());
    let res = executor.eval().unwrap();

    assert_eq!(res, "-2")
}

#[test]
fn neg_numbers_2() {
    let mut lexer = Lexer::new();
    let src = "1-2*45;";
    lexer.lex(src);

    let mut parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let executor = Executor::with_stdout(program.decls());
    let res = executor.eval().unwrap();

    assert_eq!(res, "-89")
}

#[test]
fn string_concat() {
    let mut lexer = Lexer::new();
    let src = "\"hello\"+\"hello\";";
    lexer.lex(src);

    let mut parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let executor = Executor::with_stdout(program.decls());
    let res = executor.eval().unwrap();

    assert_eq!(res, "hellohello")
}

#[test]
fn string_concat_groups() {
    let mut lexer = Lexer::new();
    let src = "(\"quz\" + \"baz\") + (\"quz\" + \"bar\");";
    lexer.lex(src);

    let mut parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let executor = Executor::with_stdout(program.decls());
    let res = executor.eval().unwrap();

    assert_eq!(res, "quzbazquzbar")
}

#[test]
fn unary_expected_num() {
    let mut lexer = Lexer::new();
    let src = r#"-"test";"#;
    lexer.lex(src);

    let mut parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let executor = Executor::with_stdout(program.decls());
    let err = executor.eval().unwrap_err();

    assert!(matches!(err.kind(), ErrorKind::MustBeNumber))
}

#[test]
fn expect_both_nums_or_strings() {
    let mut lexer = Lexer::new();
    let src = r#"// lol comment here
        "test" + 123.44;"#;
    lexer.lex(src);

    let mut parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let executor = Executor::with_stdout(program.decls());
    let err = executor.eval().unwrap_err();

    assert_eq!(err.line(), 1);
    assert!(matches!(err.kind(), ErrorKind::BothMustBeNumbersOrStrings))
}

#[test]
fn print() {
    assert_program_stdout! {
        r#"
        // lol comment here
        print 123.44;"#,
        "123.44"
    }
}

#[test]
fn multiline_with_not_ascii() {
    assert_program_stdout! {r#"
    // This program prints the result of a comparison operation
    // It also tests multi-line strings and non-ASCII characters
    print false != false;

    print "53
    17
    98
    ";

    print "There should be an empty line above this.";

    print "(" + "" + ")";

    print "non-ascii: ॐ";"#,
    "false", "53", "17", "98", "", "There should be an empty line above this.", "()", "non-ascii: ॐ"
    }
}

#[test]
fn basic_vars() {
    assert_program_stdout! {r#"
    var test = "abc";

    print test;
    print test + test;
    print test + "___" + test;"#,
    "abc",
    "abcabc",
    "abc___abc"
    }
}

#[test]
fn basic_string_vars() {
    assert_program_stdout! {r#"
        var baz = 82;
        var world = 82;
        print baz + world;
        var quz = 82;
        print baz + world + quz;"#,
        (82 * 2).to_string().as_str(),
        (82 * 3).to_string().as_str()
    }
}

#[test]
fn basic_var_reassignment() {
    assert_program_stdout! {
        r#"
        var baz = 82;
        print baz;
        baz = baz * 2;
        print baz;
        baz = baz * 2;
        print baz;"#,
        82.to_string().as_str(),
        (82 * 2).to_string().as_str(),
        (82 * 4).to_string().as_str()
    }
}

#[test]
fn multi_variable_assignment() {
    assert_program_stdout! {r#"
        var a;
        var b = 2;
        var a = b = 1;
        print a;"#,
        "1"
    }
}

#[test]
fn basic_if() {
    assert_program_stdout! {r#"
        var a = false;
        if (a = true) {
          print (a == true);
        }"#,
        "true"
    }
}

#[test]
fn many_ors() {
    assert_program_stdout! {r#"
        print 66 or true;
        print false or 66;
        print false or false or true;

        print false or false;
        print false or false or false;
        print false or false or false or false;"#,
        "66",
        "66",
        "true",
        "false",
        "false",
        "false"
    }
}

#[test]
fn for_loop() {
    assert_program_stdout! {"for (var foo = 0; foo < 3;) print foo = foo + 1;",
        "1",
        "2",
        "3"
    }
}

#[test]
fn clock() {
    let mut lexer = Lexer::new();
    let src = "for (var foo = 0; foo < 5;foo=foo+1) print clock();";
    lexer.lex(src);

    assert_eq!(lexer.errors(), [].as_slice());

    let mut parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();

    eprintln!("PROGRAM: {program:?}");

    let mut stdout: Vec<u8> = Vec::new();
    let executor = Executor::new(program.decls(), &mut stdout);
    executor.run().unwrap();

    let stdout = String::from_utf8(stdout).unwrap();
    let mut lines = stdout.lines();
    assert!(lines.next().unwrap().starts_with("17"));
    assert!(lines.next().unwrap().starts_with("17"));
    assert!(lines.next().unwrap().starts_with("17"));
    assert!(lines.next().unwrap().starts_with("17"));
    assert!(lines.next().unwrap().starts_with("17"));
    assert!(lines.next().is_none());
}

#[test]
fn basic_fn() {
    assert_program_stdout! {r#"
        fun baz() { print 97; }
        baz();
    "#,
    "97"
    }
}

#[test]
fn basic_fn_with_args() {
    assert_program_stdout! {r#"
        fun f1(a) { print a; }
        f1(49);
    "#,
    "49"
    }
}

#[test]
fn basic_fn_with_early_return() {
    assert_program_stdout! {r#"
        fun return_gte(a, b) {
            if (a >= b) {
                return a;
            } else {
                return b;
            }
        }

        print return_gte(10, 20);
        print return_gte(133, 20);
        print return_gte(-12, 20);
        print return_gte(10*34, 20);
    "#,
    "20",
    "133",
    "20",
    "340"
    }
}

#[test]
fn fib() {
    assert_program_stdout! {
      "
        fun fib(n) {
          if (n < 2) return n;
          return fib(n - 2) + fib(n - 1);
        }

        var start = clock();
        print fib(4);
        print fib(4) == 3;
        print fib(10);
        print fib(20);
    ","3",
    "true",
    "55",
    "6765"
    }
}

#[test]
fn fib2() {
    assert_program_stdout! {r#"
        var n = 10;
        var fm = 0;
        var fn = 1;
        var index = 0;

        while (index < n) {
            print fm;
            var temp = fm;
            fm = fn;
            fn = temp + fn;
            index = index + 1;
        }
    "#,
    "0",
    "1",
    "1",
    "2",
    "3",
    "5",
    "8",
    "13",
    "21",
    "34"
    }
}

#[test]
fn higher_ord_fun() {
    assert_program_stdout! {r#"
        fun makeFilter(min) {
          fun filter(n) {
            if (n < min) {
              return false;
            }
            return true;
          }
          return filter;
        }

        // This function applies a function to a list of
        // numbers
        fun applyToNumbers(f, count) {
          var n = 0;
          while (n < count) {
            if (f(n)) {
              print n;
            }
            n = n + 1;
          }
        }

        var greaterThanX = makeFilter(2);
        var greaterThanY = makeFilter(4);

        print "Numbers >= 2:";
        applyToNumbers(greaterThanX, 5);

        print "Numbers >= 4:";
        applyToNumbers(greaterThanY, 5);
    "#,
    "Numbers >= 2:",
    "2",
    "3",
    "4",
    "Numbers >= 4:",
    "4"
    }
}

#[test]
fn scopes() {
    assert_program_stdout! {r#"
        var x = 1;
        var y = 2;

        fun printBoth() {
            if (x < y) {
                print "x is less than y:";
                print x;
                print y;
            } else {
                print "x is not less than y:";
                print x;
                print y;
            }
        }

        {
            var x = 10;
            {
                var y = 20;

                // var i = 0;
                // while (i < 3) {
                //     x = x + 1;
                //     y = y - 1;
                //     print "Local x: ";
                //     print x;
                //     print "Local y: ";
                //     print y;
                //     i = i + 1;
                // }

                if (x > y) {
                    print "Local x > y";
                }

                printBoth();
            }
        }

        if (x == 1 and y == 2) {
            print "Globals unchanged:";
            printBoth();
        }
    "#,
    "x is less than y:",
    "1",
    "2",
    "Globals unchanged:",
    "x is less than y:",
    "1",
    "2"
    }
}

#[test]
fn mutable_closure() {
    assert_program_stdout! {r#"
        fun makeCounter() {
        var i = 0;
        fun count() {
            i = i + 3;
            print i;
        }

        return count;
        }

        var counter = makeCounter();
        counter();
        counter();"#,
    "3",
    "6"
    }
}

#[test]
fn call_fun_returned_from_fn() {
    assert_program_stdout! {r#"
        fun returnArg(arg) {
          return arg;
        }

        fun returnFunCallWithArg(func, arg) {
          return returnArg(func)(arg);
        }

        fun printArg(arg) {
          print arg;
        }

        returnFunCallWithArg(printArg, "foo");
        "#,
    "foo"
    }
}

#[test]
fn local_var_after_fn_decl_should_not_affect() {
    assert_program_stdout! {r#"
        var variable = "global";

        {
          fun f() {
            print variable;
          }

          f(); // this should print "global"

          // This variable declaration shouldn't affect
          // the usage in `f` above.
          var variable = "local";

          f(); // this should still print "global"
        }"#,
    "global",
    "global"
    }
}

#[test]
fn reassign_parameter() {
    assert_program_stdout! {r#"
        fun square(x) {
          return x * x;
        }

        // This higher-order function applies a
        // function N times to a starting value x.
        fun applyTimesN(N, f, x) {
          var i = 0;
          while (i < N) {
            x = f(x);
            i = i + 1;
          }
          return x;
        }

        // 5 is squared once
        print applyTimesN(1, square, 5);
        // 5 is squared twice
        print applyTimesN(2, square, 5);
        // 5 is squared thrice
        print applyTimesN(3, square, 5);
    "#,
    "25",
    "625",
    "390625"
    }
}

#[test]
fn timer() {
    assert_program_stdout! {
      r#"
        var startTime = clock();
        var lastCheck = startTime;
        var running = true;

        print "Starting timer for 0.2 seconds";
        var startTime = clock();

        while (running) {
          if (clock() > startTime + 0.2) {
            print "Timer ended";
            running = false;
          }
        }
    "#,
      "Starting timer for 0.2 seconds",
      "Timer ended"
    }
}

#[test]
fn foor_loop_variable_mutations() {
    assert_program_stdout! {r#"
        var baz = "after";
        {
          var baz = "before";

          for (var baz = 0; baz < 1; baz = baz + 1) {
            print baz;
            var baz = -1;
            print baz;
          }
        }

        {
          for (var baz = 0; baz > 0; baz = baz + 1) {}

          var baz = "after";
          print baz;

          for (baz = 0; baz < 1; baz = baz + 1) {
            print baz;
          }
        }
    "#,
    "0",
    "-1",
    "after",
    "0"
    }
}

#[test]
fn basic_class_decl_and_instantiation() {
    assert_program_stdout! {r#"
        class Rust {}
        var new = Rust();
        print Rust;
        print new;
    "#,
    "Rust",
    "Rust instance"
    }
}

#[test]
fn basic_class_properties() {
    assert_program_stdout! {r#"
        class Spaceship {}
        var falcon = Spaceship();

        // Setting properties on an instance should work
        falcon.name = "Millennium Falcon";
        falcon.speed = 75.5;

        // Getting properties on an instance should work
        print "Ship details:";
        print falcon.name;
        print falcon.speed;"#,
    "Ship details:",
    "Millennium Falcon",
    "75.5"
    }
}

#[test]
fn basic_class_methods() {
    assert_program_stdout! {r#"
        class Wizard {
          castSpell(spell) {
            // Methods should be able to accept a parameter
            print "Casting a magical spell: " + spell;
          }
        }

        class Dragon {
          // Methods should be able to accept multiple
          // parameters
          breatheFire(fire, intensity) {
            print "Breathing " + fire + " with intensity: "
            + intensity;
          }
        }

        var merlin = Wizard();
        var smaug = Dragon();

        if (false) {
          var action = merlin.castSpell;
          action("Fireball");
        } else {
          var action = smaug.breatheFire;
          action("Fire", "100");
        }"#,
    "Breathing Fire with intensity: 100"
    }
}

#[test]
fn classes_as_args_to_methods() {
    assert_program_stdout! {r#"
        class Superhero {
          // Methods should be able to accept a parameter
          useSpecialPower(hero) {
            print "Using power: " + hero.specialPower;
          }

          // Methods should be able to accept a parameter
          // of any type
          hasSpecialPower(hero) {
            return hero.specialPower;
          }

          // Methods should be able to accept class
          // instances as parameters and then update their
          // properties
          giveSpecialPower(hero, power) {
            hero.specialPower = power;
          }
        }

        fun performHeroics(hero, superheroClass) {
          if (superheroClass.hasSpecialPower(hero)) {
            superheroClass.useSpecialPower(hero);
          } else {
            print "No special power available";
          }
        }

        var superman = Superhero();
        var heroClass = Superhero();

        if (true) {
          heroClass.giveSpecialPower(superman, "Flight");
        } else {
          heroClass.giveSpecialPower(superman, "Strength");
        }

        performHeroics(superman, heroClass);
            "#,
    "Using power: Flight"}
}

#[test]
fn basic_this_usage() {
    assert_program_stdout! {
        r#"
            class Spaceship {
              identify() {
                // this should be bound to the instance
                print this;
              }
            }

            // Calling a method on a class instance should work
            Spaceship().identify();
        "#,
        "Spaceship instance"
    }
}

#[test]
fn this_bounding_check() {
    assert_program_stdout! {
        r#"
        class Animal {
          makeSound() {
            print this.sound;
          }
            
          identify() {
            print this.species;
          }
        }
            
        var dog = Animal();
        dog.sound = "Woof";
        dog.species = "Dog";
            
        var cat = Animal();
        cat.sound = "Meow";
        cat.species = "Cat";
        cat.test = "lol";

            
        // The this keyword should be bound to the
        // class instance that the method is called on
        cat.makeSound = dog.makeSound;
        dog.identify = cat.identify;

        cat.makeSound();
        dog.identify();
                   "#,
        "Woof",
        "Cat"
    }
}
#[test]
fn this_undefined_property() {
    let mut lexer = Lexer::new();
    let src = r#"
        class Confused {
            method() {
                fun inner(instance) {
                    // this is a local variable
                    var feeling = "confused";
                    // Unless explicitly set, feeling can't be
                    // accessed using this keyword
                    print this.feeling; // expect runtime error
                }
                return inner;
            }
        }

        var instance = Confused();
        var m = instance.method();
        // calling the function returned should work
        m(instance);"#;

    lexer.lex(src);

    let mut parser = Parser::new(lexer.tokens());
    let program = parser.parse().unwrap();
    let executor = Executor::with_stdout(program.decls());
    let err = executor.run().unwrap_err();

    assert!(matches!(
        err.kind(),
        ErrorKind::UndefinedProperty("feeling")
    ));
}

#[test]
fn basic_constructor() {
    assert_program_stdout! {
        r#"

        class Default {
          // this is the constructor
          init() {
            // it should be able to set
            // properties on the instance
            this.x = "quz";
            this.y = 35;
          }
        }
        
        // the constructor should be called
        // automatically  when the class is being
        // instantiated
        print Default().x;
        print Default().y;

            "#,

        "quz",
        "35"
    }
}

#[test]
fn basic_constructor_2() {
    assert_program_stdout! {
        r#"
        class Counter {
          init(startValue) {
            if (startValue < 0) {
              print "startValue can't be negative";
              this.count = 0;
            } else {
              this.count = startValue;
            }
          }
        }
        
        // constructor is called automatically here
        var instance = Counter(-43);
        print instance.count;
        
        // it should be possible to call the constructor
        // on a class instance as well
        print instance.init(43).count;
        "#,
        "startValue can't be negative",
        "0",
        "43"
    }
}

#[test]
fn basic_inherited_methods() {

    assert_program_stdout!{
        r#"
        class foo {
          infoo() {
            print "from foo";
          }
        }
        
        class hello < foo {
          inhello() {
            print "from hello";
          }
        }
        
        class world < hello {
          inworld() {
            print "from world";
          }
        }
        
        // world should inherit the methods
        // from both foo and hello
        var world = world();
        world.infoo();
        world.inhello();
        world.inworld();"#,
        "from foo",
        "from hello",
        "from world"
    }
}
