# Changelog

## [1.13.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.12.1...v1.13.0) (2026-03-09)

### Bug Fixes

- clean up output of errormonitor ([#555](https://github.com/astroautomata/SymbolicRegression.jl/issues/555)) ([210deac](https://github.com/astroautomata/SymbolicRegression.jl/commit/210deacdaf253777c3041c4749eac1898d555083))

## [1.12.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.12.0...v1.12.1) (2026-02-14)

## [2.0.0-alpha.9](https://github.com/astroautomata/SymbolicRegression.jl/compare/v2.0.0-alpha.8...v2.0.0-alpha.9) (2026-02-04)

### Features

- create AbstractPopMember ([#540](https://github.com/astroautomata/SymbolicRegression.jl/issues/540)) ([5b5a5a3](https://github.com/astroautomata/SymbolicRegression.jl/commit/5b5a5a3bd2cbc700941e1c91647fa7443398756d))

## [2.0.0-alpha.8](https://github.com/astroautomata/SymbolicRegression.jl/compare/v2.0.0-alpha.7...v2.0.0-alpha.8) (2025-08-31)

### ⚠ BREAKING CHANGES

- set adaptive_parsimony_scaling back to 20.0 on v2+

### Features

- set adaptive_parsimony_scaling back to 20.0 on v2+ ([0b4ac3c](https://github.com/astroautomata/SymbolicRegression.jl/commit/0b4ac3caa056a222c3c0d04eac480ccac7b02d0e))

### Bug Fixes

- caching of options in MLJ regressors ([51e5a3e](https://github.com/astroautomata/SymbolicRegression.jl/commit/51e5a3eb639239382208cf84e3e7b29956614ce5))
- never store member if violating constraints ([a9754ad](https://github.com/astroautomata/SymbolicRegression.jl/commit/a9754ad1d0bee0a9f20fd5d1534d0d2907d34370))
- poisson_sample for lambda=0 ([fc0bbd9](https://github.com/astroautomata/SymbolicRegression.jl/commit/fc0bbd954a3a81c12befdb5a1ef389f6923aa37e))
- preserve state when niterations=0 ([6c611f3](https://github.com/astroautomata/SymbolicRegression.jl/commit/6c611f3ab541a4bc5bc5450b64ccd309189f9d3a))

## [2.0.0-alpha.7](https://github.com/astroautomata/SymbolicRegression.jl/compare/v2.0.0-alpha.6...v2.0.0-alpha.7) (2025-08-23)

### Features

- add `worker_timeout` ([5b4a712](https://github.com/astroautomata/SymbolicRegression.jl/commit/5b4a712fd61da2ed4ab5a7b55dbca3e2a93de36c))
- handle mixed types in body of template expression ([0781cf7](https://github.com/astroautomata/SymbolicRegression.jl/commit/0781cf77246893c53fcd18220c2678ca96a0a207))
- make ComposableExpression auto-convert ([ccef1d1](https://github.com/astroautomata/SymbolicRegression.jl/commit/ccef1d15ab49d4af04dc333e5f70164db765ef98))
- nicer errors for common template expression mistakes ([3e155e5](https://github.com/astroautomata/SymbolicRegression.jl/commit/3e155e58e654a78a4cb353466fd04f6402f5ab0e))

### Bug Fixes

- should default to larger of timeouts ([f45e146](https://github.com/astroautomata/SymbolicRegression.jl/commit/f45e1465e850a8269d1d5b805450b46dd75e1761))

## [2.0.0-alpha.6](https://github.com/astroautomata/SymbolicRegression.jl/compare/v2.0.0-alpha.5...v2.0.0-alpha.6) (2025-07-30)

### Bug Fixes

- ensure we dont force OperatorEnum ([9d99fea](https://github.com/astroautomata/SymbolicRegression.jl/commit/9d99feab741f47d35772cf5e5e2af80e1a50a7f5))
- OperatorEnum gets mapped to safe operators ([ecc271e](https://github.com/astroautomata/SymbolicRegression.jl/commit/ecc271e92babfa2e5f63f0067b669ecba6b7fb89))

## [2.0.0-alpha.5](https://github.com/astroautomata/SymbolicRegression.jl/compare/v2.0.0-alpha.4...v2.0.0-alpha.5) (2025-07-29)

### Features

- always save file even if niterations=0 ([10236d7](https://github.com/astroautomata/SymbolicRegression.jl/commit/10236d70b82648e4ec02a5651cf456271641eb2f))

## [2.0.0-alpha.4](https://github.com/astroautomata/SymbolicRegression.jl/compare/v2.0.0-alpha.3...v2.0.0-alpha.4) (2025-07-28)

### ⚠ BREAKING CHANGES

- generalize delete_random_op!
- generalize \_random_op mutations to n-arity

### Features

- clean up output of errormonitor ([20fcaed](https://github.com/astroautomata/SymbolicRegression.jl/commit/20fcaed201c5c4bcbab237fe19f425b159cbf640))
- create mutation that changes a feature node ([84ba961](https://github.com/astroautomata/SymbolicRegression.jl/commit/84ba961d8ca79fedd7be0d8f57c64733fd643f7a))
- enable n-arity operators for dimensional analysis ([dbc9777](https://github.com/astroautomata/SymbolicRegression.jl/commit/dbc97770eda832218261d8686bceee9309852fb7))
- general form of `gen_random_tree_fixed_size` ([bd95031](https://github.com/astroautomata/SymbolicRegression.jl/commit/bd95031daa67a5138b4f1f5a003359cc4efb40d0))
- general form of tree rotation ([940fc78](https://github.com/astroautomata/SymbolicRegression.jl/commit/940fc789c39da2676d5fb7576c31db5cc0309e3b))
- generalize \_random_connection! logic to n-arity ([b2c85f7](https://github.com/astroautomata/SymbolicRegression.jl/commit/b2c85f73775c1079654f13b1bfd7c8cbc2a26d02))
- generalize \_random_op mutations to n-arity ([62e6758](https://github.com/astroautomata/SymbolicRegression.jl/commit/62e6758236d8c568727b1c52b072672608c41747))
- generalize append_random_op to n-arity ([c6167d1](https://github.com/astroautomata/SymbolicRegression.jl/commit/c6167d14d7bcb05ea94f30615f25659cc03c65a9))
- generalize crossover_trees ([c723dfc](https://github.com/astroautomata/SymbolicRegression.jl/commit/c723dfcf5e8ae989dd65ef480fc7247b079530d9))
- generalize delete_random_op! ([f19bdb7](https://github.com/astroautomata/SymbolicRegression.jl/commit/f19bdb74f31eaa224a24b46e1a0de7c7244c5f82))
- generalize mutate_operator ([0f884a2](https://github.com/astroautomata/SymbolicRegression.jl/commit/0f884a2336c47345c5b43ae4e00f3306c5e3ac41))
- generalize swap_operands to n-arity ([9b261f3](https://github.com/astroautomata/SymbolicRegression.jl/commit/9b261f33f134fd49f2ed5a17de54ef0591801660))
- only mutate up to the number of available features in template expressions ([738165e](https://github.com/astroautomata/SymbolicRegression.jl/commit/738165e6a213321b2869025ca83e655473d35f5c))
- permit n-arity specifications to Options ([f6ba5a1](https://github.com/astroautomata/SymbolicRegression.jl/commit/f6ba5a1e3b835ab52976c8ee105b460d988df7a9))

### Bug Fixes

- constraints for 3-arity operators ([4090fbb](https://github.com/astroautomata/SymbolicRegression.jl/commit/4090fbb5a906674c6bec1b3849c9ab0506e51810))
- issue where operators overwritten ([c8406eb](https://github.com/astroautomata/SymbolicRegression.jl/commit/c8406eb5b05290203adb368d06aaadf23fd67771))
- macro hygeine for internal macros ([ccbf692](https://github.com/astroautomata/SymbolicRegression.jl/commit/ccbf6923404aa7ec2d96e66e702080fbe8e95920))
- remove old random_node_and_parent import ([ab8f7b7](https://github.com/astroautomata/SymbolicRegression.jl/commit/ab8f7b7e4cb06fa7f4607024bd420775bff17859))
- TemplateExpression conditioning ([a5337f5](https://github.com/astroautomata/SymbolicRegression.jl/commit/a5337f500a7d9718350b7225b567e789db88bab2))
- unbound type param ([a8ad5d9](https://github.com/astroautomata/SymbolicRegression.jl/commit/a8ad5d90ae6f0e412459409aea39a3fc7aaf8054))

## [2.0.0-alpha.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v2.0.0-alpha.2...v2.0.0-alpha.3) (2025-07-27)

### Features

- enforce that TemplateExpression respected ([ac97cd6](https://github.com/astroautomata/SymbolicRegression.jl/commit/ac97cd6113a2b9a0a171ab7e203dafaca912672e))
- ensure we copy user guesses if expression ([4111469](https://github.com/astroautomata/SymbolicRegression.jl/commit/4111469c81d3e7d9905d132b6d709fb9ed214f7c))
- guesses for TemplateExpression ([b52906a](https://github.com/astroautomata/SymbolicRegression.jl/commit/b52906a1ed0364608634799f2f8c07a163490477))
- helpful debugging message for bad template expression guess ([d14ace6](https://github.com/astroautomata/SymbolicRegression.jl/commit/d14ace6ef3c70b1d3a2e098d3998b46c572d97f3))
- `guesses` parameter for SRRegressor ([236af2b](https://github.com/astroautomata/SymbolicRegression.jl/commit/236af2b340e00014e901efc9e88b45bbc6c37677))
- permanence of guesses throughout search ([c5ff3f0](https://github.com/astroautomata/SymbolicRegression.jl/commit/c5ff3f002f168865b004223dc1f8e5bffc7c84d9))
- permit guesses in equation search, using `parse_expression` utility ([1f24e09](https://github.com/astroautomata/SymbolicRegression.jl/commit/1f24e095c8a7c33c13b1f2a50269b72234bbbe98))
- warn if user passes overly complex guess ([f241a4b](https://github.com/astroautomata/SymbolicRegression.jl/commit/f241a4b41c95f40b46e43957d72561112016cc08))

### Bug Fixes

- expression guesses when parameters required ([4fe4aa0](https://github.com/astroautomata/SymbolicRegression.jl/commit/4fe4aa09b8bcef6bfa59662018aee814293a7952))
- JET errors ([3be2e79](https://github.com/astroautomata/SymbolicRegression.jl/commit/3be2e7913eba81e67e4c9cf90d85f659a87cf0f3))

### Reverts

- changes to IDE ([c25979e](https://github.com/astroautomata/SymbolicRegression.jl/commit/c25979eda2977a8a626d5f241ab55786408e8b6e))

## [2.0.0-alpha.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v2.0.0-alpha.1...v2.0.0-alpha.2) (2025-07-20)

### Features

- add back missing tangent type ([882b454](https://github.com/astroautomata/SymbolicRegression.jl/commit/882b454412f6e22fe3f103f774bab71e14835da8))
- add rng parameter to constant optimization ([4add39c](https://github.com/astroautomata/SymbolicRegression.jl/commit/4add39ca79bdf947faa052a7226a6f11dbe37e18))
- ensure Mooncake loaded on workers ([b23d1bd](https://github.com/astroautomata/SymbolicRegression.jl/commit/b23d1bd4bd93c48a2d0309e8b62878fa46b43322))
- fix enzyme calls ([31bdd80](https://github.com/astroautomata/SymbolicRegression.jl/commit/31bdd8012ebbdaf2e07b1eef5d84926f8b13ff97))
- introduce `stable_get!` for stable dictionary access ([0319b45](https://github.com/astroautomata/SymbolicRegression.jl/commit/0319b455819696c5f608936b2d4e656c1d936146))
- make enzyme backend more general with `make_zero` ([e7641a4](https://github.com/astroautomata/SymbolicRegression.jl/commit/e7641a4abd450006b18c24f5303bf017d731374e))
- make `has_params` available in top level ([9f3d1b2](https://github.com/astroautomata/SymbolicRegression.jl/commit/9f3d1b2ccd306bd2f823211d024fed2556e075d0))
- Mooncake extension ([0a5a919](https://github.com/astroautomata/SymbolicRegression.jl/commit/0a5a91954c7701e64f29310217c36d33ccb89335))

### Bug Fixes

- Enzyme integration (still broken though) ([e47f081](https://github.com/astroautomata/SymbolicRegression.jl/commit/e47f081278316bc936850688bcd2e336385373d7))
- incorrect type declaration ([89e4a2b](https://github.com/astroautomata/SymbolicRegression.jl/commit/89e4a2b9f5ee4ee92b15360d6b0807ebb0cc8d96))
- issue where minimizer is not loaded to tree ([dbf6513](https://github.com/astroautomata/SymbolicRegression.jl/commit/dbf65135e72f45541812ab3123b4a9e5f0c322ed))
- mooncake missing tangent type ([734257b](https://github.com/astroautomata/SymbolicRegression.jl/commit/734257bd6bfdbc11fe0bc9d12491e61c1836c737))
- parameter count through template expressions ([65128a1](https://github.com/astroautomata/SymbolicRegression.jl/commit/65128a1db48efa87a3e0e8f79fb4b1c08151324a))
- prep caching based on tree type ([0f99a7a](https://github.com/astroautomata/SymbolicRegression.jl/commit/0f99a7a3ff56d19f03eaf98a691835f720f0a30d))
- remove redundant tangent_type overload ([4412b39](https://github.com/astroautomata/SymbolicRegression.jl/commit/4412b398fb07e1d951471424013f2b5bf5bf3f45))
- safe overload of tangent type ([7c82d43](https://github.com/astroautomata/SymbolicRegression.jl/commit/7c82d43156477f8b6666571522cf955f7681dcb9))
- type instabilities in optimization ([f76bece](https://github.com/astroautomata/SymbolicRegression.jl/commit/f76bece708a30953dda2f5a389de1f11b4c6035d))

## [2.0.0-alpha.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.12.0...v2.0.0-alpha.1) (2025-06-24)

### Features

- initial support for DE.jl 2.0 ([88dc037](https://github.com/astroautomata/SymbolicRegression.jl/commit/88dc0377078c62b4d6448387725a9f2d629b09d6))

### Bug Fixes

- infer max degree from operators or user-provided ([0bada8c](https://github.com/astroautomata/SymbolicRegression.jl/commit/0bada8c9242cf45608d66786ccfd3919cac4275f))

## [1.12.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.11.3...v1.12.0) (2025-06-24)

### Bug Fixes

- issue where minimizer is not loaded to tree ([f0ff1a0](https://github.com/astroautomata/SymbolicRegression.jl/commit/f0ff1a01e48a30b19effe6d610dd571f9ed4dfd0))

## [1.11.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.11.2...v1.11.3) (2025-06-15)

## [1.11.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.11.1...v1.11.2) (2025-06-12)

## [1.11.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.11.0...v1.11.1) (2025-05-20)

### Features

- enable template expressions in a distributed setting ([4c96cc9](https://github.com/astroautomata/SymbolicRegression.jl/commit/4c96cc90de73e8db3cab7f422c8e3ea69cfbf0a3))

### Bug Fixes

- use generic interface for worker distribution ([6311632](https://github.com/astroautomata/SymbolicRegression.jl/commit/6311632d772d1f2665cc98c009353ed945999d1d))

## [1.11.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.10.0...v1.11.0) (2025-05-18)

### Features

- allow `@template_spec` to declare explicit num_features ([ebb1a80](https://github.com/astroautomata/SymbolicRegression.jl/commit/ebb1a80f449fa608670a8565fc319e8f42d37a2c))
- allow negative losses ([fc9fcdb](https://github.com/astroautomata/SymbolicRegression.jl/commit/fc9fcdbfac515efe2b53e1af0ee7f7cdeb23986a))
- avoid use of scores when assuming negative losses ([996d930](https://github.com/astroautomata/SymbolicRegression.jl/commit/996d93097b447a379873be72484b78e2d1d5aff8))
- move `get_options` into top namespace ([3726466](https://github.com/astroautomata/SymbolicRegression.jl/commit/37264668adcb06279ea23f203ca91bcf99d4caae))
- recommend users use TemplateExpressionSpec instead ([ad07294](https://github.com/astroautomata/SymbolicRegression.jl/commit/ad072940ad2deb9c9b588645b2cf6e44e0fab664))

### Bug Fixes

- avoid printing heap size hint if already created ([4334193](https://github.com/astroautomata/SymbolicRegression.jl/commit/43341939ad9b1224de60254dfc1e7c3bfe7cb321))
- Enzyme extension (up to issues of Enzyme itself) ([8f32e96](https://github.com/astroautomata/SymbolicRegression.jl/commit/8f32e9689c823a61277b19224b789a7c59ce2090))
- per task cache can be immutable ([2a8663c](https://github.com/astroautomata/SymbolicRegression.jl/commit/2a8663c0040baf1fe394fd54b6c725fda6e08768))
- scope error in hall of fame formatting ([64c994d](https://github.com/astroautomata/SymbolicRegression.jl/commit/64c994d9c4f9569882a0c24fb7259c077e5696f7))

## [1.10.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.9.3...v1.10.0) (2025-05-01)

### Features

- finish remaining parts of string interface ([247f533](https://github.com/astroautomata/SymbolicRegression.jl/commit/247f53316f4fe4cd88eb2314b44c38dfe194c738))
- initial compat with string features ([008cdc1](https://github.com/astroautomata/SymbolicRegression.jl/commit/008cdc19d327424c419921f74024ed8e2f8672ed))

## [1.9.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.9.2...v1.9.3) (2025-04-25)

### Bug Fixes

- unary constraint check missed ([bfbb254](https://github.com/astroautomata/SymbolicRegression.jl/commit/bfbb2546128bb2704ff08770d58443c8fa79007c))

## [1.9.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.9.1...v1.9.2) (2025-04-10)

## [1.9.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.9.0...v1.9.1) (2025-04-04)

## [1.9.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.8.0...v1.9.0) (2025-03-01)

### Bug Fixes

- printing greater and lesser ([d5f6fbd](https://github.com/astroautomata/SymbolicRegression.jl/commit/d5f6fbd1aacd1a5fe7dc9c6729d6dacf29b61830))

## [1.8.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.7.2...v1.8.0) (2025-02-22)

### Features

- allow recording crossovers ([#415](https://github.com/astroautomata/SymbolicRegression.jl/issues/415)) ([23a4f2e](https://github.com/astroautomata/SymbolicRegression.jl/commit/23a4f2e7dbd86b6ab1f5f7c71d519ec16b906840))
- better error for mismatched eltypes ([68d6397](https://github.com/astroautomata/SymbolicRegression.jl/commit/68d63978d414940a9c492bd1b75471173120fe1e))
- explicitly monitor errors in workers ([b86b4c1](https://github.com/astroautomata/SymbolicRegression.jl/commit/b86b4c1ed37328b83635d2f5fa7d826d84092c7a))
- generic getters for datasets ([3b923bd](https://github.com/astroautomata/SymbolicRegression.jl/commit/3b923bd65a7bd16d629a054f07e3e680e4da1022))
- utility functions for batching dataset ([bb406ed](https://github.com/astroautomata/SymbolicRegression.jl/commit/bb406edb0c137bbcca3cefcb64d0d02b5406b38e))

### Bug Fixes

- batched dataset for optimisation ([d085fd8](https://github.com/astroautomata/SymbolicRegression.jl/commit/d085fd837e323d82bf363f4e8f986bd6ab5fb5f9))
- only optimize hall of fame if exists ([cc3a8a5](https://github.com/astroautomata/SymbolicRegression.jl/commit/cc3a8a52b3f6e90fc847e4bebd2694a143455f95))
- parametric expressions batching ([2d6f665](https://github.com/astroautomata/SymbolicRegression.jl/commit/2d6f665bc327f6a1ee5a9c9d04b48c99afcc17e7))

## [1.7.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.7.1...v1.7.2) (2025-02-13)

### Bug Fixes

- max of 6 expressions bug ([fcb03d9](https://github.com/astroautomata/SymbolicRegression.jl/commit/fcb03d9c9692df5d8e756d35653f3206c1a914a1))

## [1.7.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.7.0...v1.7.1) (2025-02-09)

### Bug Fixes

- loss_function_expression in distributed mode ([c7877f3](https://github.com/astroautomata/SymbolicRegression.jl/commit/c7877f3aeae2719926cbf24d16382e65daf3756c))

## [1.7.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.6.0...v1.7.0) (2025-02-08)

### Features

- add max and min ([8d0d34d](https://github.com/astroautomata/SymbolicRegression.jl/commit/8d0d34d649f3cd04a1f5b71cba478659cd404e68))
- allow initializing parameters from naked array ([99b1598](https://github.com/astroautomata/SymbolicRegression.jl/commit/99b1598d722a62f7c0be3ecc70ad07da9ddbb719))
- allow multiple parameter keys in TemplateExpression ([fb0e21c](https://github.com/astroautomata/SymbolicRegression.jl/commit/fb0e21c99cd94771a846833605f18aefaf00196a))
- allow no parameters in `@template` macro ([204be7e](https://github.com/astroautomata/SymbolicRegression.jl/commit/204be7e569f80ee60cfcf92eed46f562f15fab44))
- automatically map comparison operators ([d08c5d7](https://github.com/astroautomata/SymbolicRegression.jl/commit/d08c5d79669d57a67ccffedefdcbee2fd9a9781b))
- create `num_params`1 argument ([f8b1ad0](https://github.com/astroautomata/SymbolicRegression.jl/commit/f8b1ad03d7246a8df0a39ae341f677d058f1767e))
- custom `mutate_constant` for parametric template expression ([a71a545](https://github.com/astroautomata/SymbolicRegression.jl/commit/a71a54576d0586228952b935ee6b8bbc81c49581))
- export expression spec ([fc2df00](https://github.com/astroautomata/SymbolicRegression.jl/commit/fc2df005a28a601405385821e236289eef7c33e2))
- have TemplateExpression store all parameters in raw string ([5e62569](https://github.com/astroautomata/SymbolicRegression.jl/commit/5e62569c584554e0ccf440e6fbf4ec6033d963e2))
- introduce `ExpressionSpec` ([f48e74c](https://github.com/astroautomata/SymbolicRegression.jl/commit/f48e74ced0eea6d9744ddacce8e4f0fbb18a58d2))
- introduce parameter feature for `TemplateExpression` ([5c5a07e](https://github.com/astroautomata/SymbolicRegression.jl/commit/5c5a07e031778499fd2f7cdd5841fd63d1512c38))
- macro for easy template expressions ([3c076e9](https://github.com/astroautomata/SymbolicRegression.jl/commit/3c076e9fbb6e5cd6488f6ee0eb5f8358be00a2c4))
- overload additional operations for ComposableExpression ([437a9ca](https://github.com/astroautomata/SymbolicRegression.jl/commit/437a9ca46547aea79950e63e010b9ab99438b30e))
- permit `variable_names=nothing` in `ComposableExpression` ([e478322](https://github.com/astroautomata/SymbolicRegression.jl/commit/e478322b1bde9fb6e02d7695dc5ec294a59f373c))
- remove node type option for TemplateExpression ([b279002](https://github.com/astroautomata/SymbolicRegression.jl/commit/b279002406ef18e567e758963387ab1c66732544))
- rename `num_params`5 to `num_params`6 ([bb927ef](https://github.com/astroautomata/SymbolicRegression.jl/commit/bb927ef271b88858a106de503d05b949a4b52880))
- safety checks for `@template` macro ([91ee759](https://github.com/astroautomata/SymbolicRegression.jl/commit/91ee759fbcb637936fed0b5eeee7b2055df799cf))
- warn for `num_params`2 and `num_params`3 ([2d9c0d8](https://github.com/astroautomata/SymbolicRegression.jl/commit/2d9c0d8d7f677005fd5e494a01d7e4606d336fbc))

### Bug Fixes

- better defensive coding ([7faeb4d](https://github.com/astroautomata/SymbolicRegression.jl/commit/7faeb4d4837675c4cb4b2520b6f95e06fc977a31))
- condition for constant mutation of template ([8f1b7dc](https://github.com/astroautomata/SymbolicRegression.jl/commit/8f1b7dc9a6884c8fe9f30b3a951cab5fe028017a))
- jet error ([415fc5c](https://github.com/astroautomata/SymbolicRegression.jl/commit/415fc5cb5cfe95e5eb3f9eff882e64b743ef881e))
- JET flagged issue ([432d7a5](https://github.com/astroautomata/SymbolicRegression.jl/commit/432d7a5b12b24fcb41d7ebc0c871edc7143ea7fc))
- missing import ([ab53c16](https://github.com/astroautomata/SymbolicRegression.jl/commit/ab53c164b0b77187da1703d1d9412446bad0c60b))
- param assertion ([a42aa91](https://github.com/astroautomata/SymbolicRegression.jl/commit/a42aa91def83b1a07b6de8e9ff4a177f396c8844))
- some issues in TemplateExpression ([29c5e4c](https://github.com/astroautomata/SymbolicRegression.jl/commit/29c5e4c91dd73b0e37d15addcb53b5fba5a23a16))
- type definition ([5b8ba79](https://github.com/astroautomata/SymbolicRegression.jl/commit/5b8ba79cbd807afdf5f5684d252c1448d66c1ee4))

## [1.6.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.5.2...v1.6.0) (2025-02-02)

### Bug Fixes

- allow for variable `nthreads` ([d29742b](https://github.com/astroautomata/SymbolicRegression.jl/commit/d29742b9687400c2d6aced5379670b25e7479189))

## [1.5.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.5.1...v1.5.2) (2025-01-03)

### Features

- conditionally widen MLJ scitype ([21443d4](https://github.com/astroautomata/SymbolicRegression.jl/commit/21443d49d74881f4896abf1d6ba79d887177f45b))
- introduce new trait for special class column ([01e3bfc](https://github.com/astroautomata/SymbolicRegression.jl/commit/01e3bfc28862c012733228fc8ccbc2489e1c39b0))

### Bug Fixes

- ambiguity in target scitype ([ea27c1a](https://github.com/astroautomata/SymbolicRegression.jl/commit/ea27c1a2e08cb84b87cba6e5067ddd65bef3702d))
- make `:class` col more generic to `X` type ([864eb63](https://github.com/astroautomata/SymbolicRegression.jl/commit/864eb6392e7bcb06eb5401389dc2eddda8aea2e7))
- pass eval options through TemplateExpression ([40cca0e](https://github.com/astroautomata/SymbolicRegression.jl/commit/40cca0ebbfce1ec0d9af44ebc0bb72956f2664c7))
- switch to `Unknown` rather than `Any` ([9f82c13](https://github.com/astroautomata/SymbolicRegression.jl/commit/9f82c13666a326d4fd560382001abb2ccda59102))

## [1.5.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.5.0...v1.5.1) (2024-12-26)

### Bug Fixes

- add missing `literal_pow` ([2a92af1](https://github.com/astroautomata/SymbolicRegression.jl/commit/2a92af1464c80edcf68b7fd8bc769deed545296d))
- higher order safe operators ([12449ca](https://github.com/astroautomata/SymbolicRegression.jl/commit/12449ca4451fbd3867063a81d4f25c83f90b37ba))
- zero-arg ComposableExpression when nan ([d875abb](https://github.com/astroautomata/SymbolicRegression.jl/commit/d875abb1581e9062691bc9c72ef079981fc1520b))

## [1.5.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.4.0...v1.5.0) (2024-12-14)

### Features

- add safe versions of `asin` and `acos` ([42dfd8d](https://github.com/astroautomata/SymbolicRegression.jl/commit/42dfd8d145cc182adc08e72ab2ed4093f1eb152e))
- create `safe_atanh` operator ([f5a41e7](https://github.com/astroautomata/SymbolicRegression.jl/commit/f5a41e7963321ce2b2576daf1a8e64d692a1b7f5))
- make safe operators compatible with ForwardDiff ([58ade27](https://github.com/astroautomata/SymbolicRegression.jl/commit/58ade27e87eb9f2cb7b28342a6834974cf4b296d))

## [1.4.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.3.1...v1.4.0) (2024-12-13)

### Features

- dynamic autodiff integration ([edcb9ed](https://github.com/astroautomata/SymbolicRegression.jl/commit/edcb9ed66bb84e70242e40acdf44e1f76e5b0eab))
- re-use allocations within mutation loop ([bf1c521](https://github.com/astroautomata/SymbolicRegression.jl/commit/bf1c52134a80e8951446fe93f9f69d7b9e6f5b27))
- reduce allocations within `next_generation` ([530689f](https://github.com/astroautomata/SymbolicRegression.jl/commit/530689fdcb3660bbab55b55c90c7224675092445))

### Bug Fixes

- allocate node storage for actual size ([adcdf15](https://github.com/astroautomata/SymbolicRegression.jl/commit/adcdf154ad541d25cbbfd086b89deb24e24510ef))
- ensure right size for preallocated storage ([399b86a](https://github.com/astroautomata/SymbolicRegression.jl/commit/399b86a8e350567bd333be65a50c6eb4ca41a88d))
- prealloc for template expressions ([693ef01](https://github.com/astroautomata/SymbolicRegression.jl/commit/693ef0180fc678220f4994c9a42c57620f4b7bd8))
- prealloc was unused ([a397dad](https://github.com/astroautomata/SymbolicRegression.jl/commit/a397dad099aaaabc96156ddf50c1a9ccc22d6dbb))

## [1.3.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.3.0...v1.3.1) (2024-12-11)

### Bug Fixes

- ambiguity in TemplateExpression ([652ea0b](https://github.com/astroautomata/SymbolicRegression.jl/commit/652ea0b7330e1745e523fa8462ebabcdba1b8f24))

## [1.3.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.2.0...v1.3.0) (2024-12-09)

### Features

- add printing for DivMonomial ([f5f7637](https://github.com/astroautomata/SymbolicRegression.jl/commit/f5f7637a5b6288af38ea85a02b59c2ae42c0e62f))
- allow user-specified `stdin` ([457c9cc](https://github.com/astroautomata/SymbolicRegression.jl/commit/457c9cc8ec3506beff38c871b5de4e98b9735cfe))
- automatic simplification in derivatives ([2c2d9fc](https://github.com/astroautomata/SymbolicRegression.jl/commit/2c2d9fcfac6fb5ca04016d2fac373dffb0000bb0))
- derivative operator for ComposableExpression ([015ac95](https://github.com/astroautomata/SymbolicRegression.jl/commit/015ac952b3860aeb4b29a5dbf02e6f572c2cfdbd))
- derivative speed hack for no dependence on variable ([39da124](https://github.com/astroautomata/SymbolicRegression.jl/commit/39da124f542fe8ce97bb4692bff2d2bd367b4c30))
- heavier automatic simplification in derivatives ([72e21fe](https://github.com/astroautomata/SymbolicRegression.jl/commit/72e21fea11328f0bc90e819c89c6ff521bc78281))
- include pretty printing of derivative operators ([73584d3](https://github.com/astroautomata/SymbolicRegression.jl/commit/73584d3189c7985b53bb429ee8ee29b861230970))
- make `D` operator compatible with TemplateExpression ([410e882](https://github.com/astroautomata/SymbolicRegression.jl/commit/410e88259611b59dce20e8541a4eead8ac6fe715))
- prefer ForwardDiff over Zygote for ComposableExpression derivatives ([74d2d33](https://github.com/astroautomata/SymbolicRegression.jl/commit/74d2d33331e6051072617f111588ff608d1d5058))
- simplify common derivatives ([472f0a7](https://github.com/astroautomata/SymbolicRegression.jl/commit/472f0a7bb14b00c3dc3340f41548a98311d3f01c))
- use newer `_zygote_gradient` operators ([3db5f99](https://github.com/astroautomata/SymbolicRegression.jl/commit/3db5f99f45352a21e4e2b91d3f56b05c5ebc103a))

### Bug Fixes

- old imports ([e05da70](https://github.com/astroautomata/SymbolicRegression.jl/commit/e05da7070973f126efa3855da24013acaa985351))

## [1.2.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.1.0...v1.2.0) (2024-12-08)

### Bug Fixes

- add missing `condition_mutation_weights!` to fix [#378](https://github.com/astroautomata/SymbolicRegression.jl/issues/378) ([f0027f4](https://github.com/astroautomata/SymbolicRegression.jl/commit/f0027f4174e577279d2c7be08ec2531688fbcc18))
- add missing `count_scalar_constants` for TemplateExpression ([802a370](https://github.com/astroautomata/SymbolicRegression.jl/commit/802a370838809f63e468061c4fc9bf9e84029734))

## [1.1.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.0.3...v1.1.0) (2024-12-03)

### Features

- allow passing additional extensions for worker imports ([788ce37](https://github.com/astroautomata/SymbolicRegression.jl/commit/788ce37f48c9106a95c2158be3aa137a0cea8bca))

### Bug Fixes

- distributed TensorBoardLogging ([272195e](https://github.com/astroautomata/SymbolicRegression.jl/commit/272195e8057693d4908800c66ed5c7f1d8c11548))

## [1.0.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.0.2...v1.0.3) (2024-11-28)

### Features

- allow argument-less TemplateExpression parts ([f4c0d7c](https://github.com/astroautomata/SymbolicRegression.jl/commit/f4c0d7c51b83fa52d39be23f5359db93c126bc44))

### Bug Fixes

- `predict` for TemplateExpressions ([808bd10](https://github.com/astroautomata/SymbolicRegression.jl/commit/808bd10111a1232ec722f1f6a89ffb7a4417bb68))

## [1.0.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.0.1...v1.0.2) (2024-11-24)

### Bug Fixes

- widen type constraints for TemplateExpression ([b5fc8eb](https://github.com/astroautomata/SymbolicRegression.jl/commit/b5fc8eb63bbd48444266c6dcb862c88ead7717db))

## [1.0.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.0.0...v1.0.1) (2024-11-20)

## [1.0.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.0.0-beta4...v1.0.0) (2024-11-15)

### Features

- change sampling of TemplateExpression ([52c933c](https://github.com/astroautomata/SymbolicRegression.jl/commit/52c933c1b08bbbc8608015b42ec1e20b1ed9723c))
- put summary statistics in separate dict ([6466213](https://github.com/astroautomata/SymbolicRegression.jl/commit/64662136e08d3847b9853ddb0a9230eb82d0a130))
- update default logging interval ([77fe278](https://github.com/astroautomata/SymbolicRegression.jl/commit/77fe27880df6cedb42c861ae7814655b2689be9a))

### Bug Fixes

- update MLJ defaults ([9e89815](https://github.com/astroautomata/SymbolicRegression.jl/commit/9e89815851a2751d3956631dff025f5b9c6a6127))

## [1.0.0-beta4](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.0.0-beta3...v1.0.0-beta4) (2024-11-09)

### ⚠ BREAKING CHANGES

- remove plotting utility

### Features

- make prefix better for template expressions ([0f5d1bf](https://github.com/astroautomata/SymbolicRegression.jl/commit/0f5d1bfb469e3997df0395157ca80a158c2d39dc))
- remove plotting utility ([e40cc01](https://github.com/astroautomata/SymbolicRegression.jl/commit/e40cc01feab37fe606e6c0d4959dc826616533eb))

### Bug Fixes

- MLJ warm start ([ea91a61](https://github.com/astroautomata/SymbolicRegression.jl/commit/ea91a613a3671448cdd8d6968ec7aa14499b1ada))
- MLJ with logger ([87cdffe](https://github.com/astroautomata/SymbolicRegression.jl/commit/87cdffe6a5c5c717144f41666fd2a92f6ba7fb55))
- update MLJ niterations ([29e3615](https://github.com/astroautomata/SymbolicRegression.jl/commit/29e361592b60cdbf324d4930583a50006a80232c))

## [1.0.0-beta3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.0.0-beta2...v1.0.0-beta3) (2024-11-07)

### ⚠ BREAKING CHANGES

- fully deprecate varMap
- move `HierarchicalExpression` into place of `TemplateExpression`
- rename `classes` to `class`

### Features

- allow custom complexity functions ([ee19066](https://github.com/astroautomata/SymbolicRegression.jl/commit/ee190666a3d2a63491f1713c3865e5e7d4bcfe01))
- better printing for HierarchicalExpression ([81b1870](https://github.com/astroautomata/SymbolicRegression.jl/commit/81b18702f1b478f9ba917f5979c42a5a21058de5))
- create `ComposableExpression` ([effab2c](https://github.com/astroautomata/SymbolicRegression.jl/commit/effab2c58415c131fbf13ab82d4d1cfcfd8ef822))
- enable `VectorWrapper` for other operators ([bc48fcc](https://github.com/astroautomata/SymbolicRegression.jl/commit/bc48fcc493bf395d4a1da550f24ab11b86472f62))
- ensure we save the full expression string ([a05bb16](https://github.com/astroautomata/SymbolicRegression.jl/commit/a05bb16c91288577ecfa55a76216e93b0bdaed73))
- expose VectorWrapper ([666babd](https://github.com/astroautomata/SymbolicRegression.jl/commit/666babd1da702735a736de336413e9fa5099fefe))
- info dump at end of search ([b517a8d](https://github.com/astroautomata/SymbolicRegression.jl/commit/b517a8da417c72dee41705642d77e6d78159c020))
- init hierarchical expression ([a1e192c](https://github.com/astroautomata/SymbolicRegression.jl/commit/a1e192caddfb9f1a77921d7dfd1d33cb950d9d54))
- make hierarchical expressions compatible ([05419e4](https://github.com/astroautomata/SymbolicRegression.jl/commit/05419e46681a780c8e92716b1797fef2c50f2003))
- move `HierarchicalExpression` into place of `TemplateExpression` ([dc2d509](https://github.com/astroautomata/SymbolicRegression.jl/commit/dc2d50975077a4089b45de1ec290ad96dbd1e784))
- print with `=` to not have breaks ([15a6159](https://github.com/astroautomata/SymbolicRegression.jl/commit/15a6159fb3da55ea6f958281a5aa7de129adf0c3))
- return `VectorWrapper`0 for invalid result rather than `VectorWrapper`1 ([6ef8bcf](https://github.com/astroautomata/SymbolicRegression.jl/commit/6ef8bcfa88470223acbb97c9ec13472fba7e7611))
- tweak names of internal types ([42935fc](https://github.com/astroautomata/SymbolicRegression.jl/commit/42935fc7ff02549754604bb0224d052271996a12))
- validation of inferred constraints ([eca9b91](https://github.com/astroautomata/SymbolicRegression.jl/commit/eca9b91db9ec637963b86646c951fe6aeeb48d82))

### Bug Fixes

- copying complexity function to worker ([9f0261d](https://github.com/astroautomata/SymbolicRegression.jl/commit/9f0261de8d5fbc9d8dc4979887464a653e6ea7fb))
- correct return type for `get_tree` ([d4c84dc](https://github.com/astroautomata/SymbolicRegression.jl/commit/d4c84dc4f2c4e4dd622f3104c870e0a10651bb62))
- fix old use of `pretty` ([cdfaaca](https://github.com/astroautomata/SymbolicRegression.jl/commit/cdfaaca2a8a31574e0fd5a130010caeb821c8f21))
- HierarchicalExpression instabilities ([c3aa38b](https://github.com/astroautomata/SymbolicRegression.jl/commit/c3aa38be7e542655312db78936c955c373182c0e))
- JET error ([91fbee9](https://github.com/astroautomata/SymbolicRegression.jl/commit/91fbee96127bbe94d0fb4e8efe8b6111d941a272))
- left arg in ComposableExpression ([e5bfeff](https://github.com/astroautomata/SymbolicRegression.jl/commit/e5bfeffba254ec4d3d0d7aa1d9fefc6b17c78a31))
- map to safe operators within ComposableExpression ([8050cd3](https://github.com/astroautomata/SymbolicRegression.jl/commit/8050cd326d7231d47913fe8aa372d5790ed13053))
- move back NodeSampler to exports ([8e438ca](https://github.com/astroautomata/SymbolicRegression.jl/commit/8e438cae7dba4c72fd61e96256d1bc653ff8501f))
- move `VectorWrapper`3 to end for precompilation ([d59de9b](https://github.com/astroautomata/SymbolicRegression.jl/commit/d59de9b202c548a5cffaad23af8e65f6e1c2b14e))
- need to freeze operators in HierarchicalExpression and ComposableExpression ([756a2d9](https://github.com/astroautomata/SymbolicRegression.jl/commit/756a2d95b724ca76269f2066bf65c0e7d06e9da0))
- reference to classes ([a59d77a](https://github.com/astroautomata/SymbolicRegression.jl/commit/a59d77a17b1e5536171a3aa940dc4fa751cbeaac))
- switch to `pretty` over `raw` ([609b7da](https://github.com/astroautomata/SymbolicRegression.jl/commit/609b7da0bb2966997334ebdf26e621a798ad8cb2))
- validate degree 2 nans ([1d22351](https://github.com/astroautomata/SymbolicRegression.jl/commit/1d22351c67b7eee78b7ec07fb6148d046586b1d5))
- validate keys of `VectorWrapper`4 ([4a7bf35](https://github.com/astroautomata/SymbolicRegression.jl/commit/4a7bf35fef9da12187c614abed86e4074118587f))

### Code Refactoring

- fully deprecate varMap ([cf631f8](https://github.com/astroautomata/SymbolicRegression.jl/commit/cf631f8b7a5f336a7aa6e946a2824f5654cfcc4a))
- rename `VectorWrapper`6 to `VectorWrapper`7 ([0df7014](https://github.com/astroautomata/SymbolicRegression.jl/commit/0df70145c4734f33ab7f131e63c3e59c6bbdeed7))

## [1.0.0-beta2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.0.0-beta1...v1.0.0-beta2) (2024-10-30)

### ⚠ BREAKING CHANGES

- default maxsize now 30
- store CSV in `outputs` folder
- MLJ saving unicode to csv
- impose new default search hyperparameters
- increase default `niterations`
- modify default hyperparameters

### Features

- accommodate newlines in equation strings ([f59186b](https://github.com/astroautomata/SymbolicRegression.jl/commit/f59186b05001598e8ab6b48973b99d3c93cdd0c5))
- add default options selector ([c6501be](https://github.com/astroautomata/SymbolicRegression.jl/commit/c6501bea987c98f9e340bc3f2bdec379282a8698))
- add other defaults to `AbstractRuntimeOptions`9 ([4617b35](https://github.com/astroautomata/SymbolicRegression.jl/commit/4617b35c10221120d6ee5bf8cfe69eb54b01d18c))
- allow custom evaluation for ConstrainedExpression ([4ce678d](https://github.com/astroautomata/SymbolicRegression.jl/commit/4ce678d2c9179b44c410c91ccc5ff12109172bab))
- callable TemplateExpression ([108d1c1](https://github.com/astroautomata/SymbolicRegression.jl/commit/108d1c18716fcfafa21747bcb1c6b47c07daa492))
- color outputs of TemplateExpression ([8a4ce91](https://github.com/astroautomata/SymbolicRegression.jl/commit/8a4ce91a7807875ab488463665f1e3caee63d6e2))
- create abstract search state class ([aa12f30](https://github.com/astroautomata/SymbolicRegression.jl/commit/aa12f30c1d2512c0a967e33ecfd07f607694580c))
- create `AbstractOptions`, `AbstractRuntimeOptions`, `AbstractMutationWeights` ([5e0053d](https://github.com/astroautomata/SymbolicRegression.jl/commit/5e0053d2f1f43d5f92e95117f690ae39fc39822e))
- declare safe operators to have easy aliases ([b587afa](https://github.com/astroautomata/SymbolicRegression.jl/commit/b587afa13d9521e090a0325a9f21c6874cf6150f))
- default maxsize now 30 ([10abb4f](https://github.com/astroautomata/SymbolicRegression.jl/commit/10abb4f166c1ccfac7c9741b8d4843d256f8cbef))
- export `AbstractOptions`3 and `AbstractOptions`4 ([e71ec07](https://github.com/astroautomata/SymbolicRegression.jl/commit/e71ec0731c7dd8635b7adbd56bae1823932d53e9))
- generalize MLJ interface ([9ed392c](https://github.com/astroautomata/SymbolicRegression.jl/commit/9ed392c2d55c04a110e00e6b5d0e31dba34aa27b))
- give reduced complexity for constrained expressions ([2e0867b](https://github.com/astroautomata/SymbolicRegression.jl/commit/2e0867bc89d29b430c539acacf063baa27b65e4e))
- impose new default search hyperparameters ([062a9dc](https://github.com/astroautomata/SymbolicRegression.jl/commit/062a9dccb3a249ffba51da27a8bd4fd4f193a433))
- improve printing styling for multi-line output ([be2fccb](https://github.com/astroautomata/SymbolicRegression.jl/commit/be2fccb92c3c3533a72eda32b557db21a5fc6ed2))
- increase default `AbstractMutationWeights`0 ([c9bd7db](https://github.com/astroautomata/SymbolicRegression.jl/commit/c9bd7db4873d0501258427f117bf760cf86c8fd4))
- initial implementation of ConstrainedExpression ([87d37aa](https://github.com/astroautomata/SymbolicRegression.jl/commit/87d37aa17a60fba8f1223cb09436b6e810342416))
- introduce `AbstractRuntimeOptions`5 for cleaner `AbstractRuntimeOptions`6 ([88a80ae](https://github.com/astroautomata/SymbolicRegression.jl/commit/88a80ae3c6e20e0b6a530691914a6b172226d56e))
- modify default hyperparameters ([7e5e517](https://github.com/astroautomata/SymbolicRegression.jl/commit/7e5e517835ab676d15f776b727b291ba60f78e2d))
- permit complex structured output ([0514bca](https://github.com/astroautomata/SymbolicRegression.jl/commit/0514bcaf817f0c622de127f0d8fad316278f6527))
- refactor mutations to enable user overloading ([44ecc12](https://github.com/astroautomata/SymbolicRegression.jl/commit/44ecc1265139ad92384e71f2d7642aadf96c8fea))
- round best hparams to 3 sig digits ([06ce20d](https://github.com/astroautomata/SymbolicRegression.jl/commit/06ce20da4ae0227a9f093a9c913a63a74c5422e2))
- store CSV in `AbstractRuntimeOptions`8 folder ([dde3d83](https://github.com/astroautomata/SymbolicRegression.jl/commit/dde3d83b9b0f643f44b44dbbe5e7f4e8808a1aa2))
- stylize printout ([5af1357](https://github.com/astroautomata/SymbolicRegression.jl/commit/5af1357dfcc83ec95cde00ae0d7d01af016cade8))
- switch from ProgressBars.jl to ProgressMeter.jl ([38cbe09](https://github.com/astroautomata/SymbolicRegression.jl/commit/38cbe0981eb4431c09720f3a65f6a771192cbc4a))
- variable constraint checking ([2d9d634](https://github.com/astroautomata/SymbolicRegression.jl/commit/2d9d634e540ceb421e8fd04197c8fa1b8f15c339))
- weight TemplateExpression sampling by num nodes ([a9e5332](https://github.com/astroautomata/SymbolicRegression.jl/commit/a9e5332c7a335eac9a8149a2119c62045f78691d))

### Bug Fixes

- add expected array type for type mismatch ([2ff1e2b](https://github.com/astroautomata/SymbolicRegression.jl/commit/2ff1e2b4ce036c092d9644bd808cea83bdaf1346))
- aliasing issue in `simplify` with extra copy ([bb86777](https://github.com/astroautomata/SymbolicRegression.jl/commit/bb86777c33745e089c2ed9fcd7e2589561762fac))
- annealing issue ([00af0ac](https://github.com/astroautomata/SymbolicRegression.jl/commit/00af0ac16632e101a6cc9430a85ee0c8c8b74c9e))
- bug in option specialization affecting Enzyme ([93e1238](https://github.com/astroautomata/SymbolicRegression.jl/commit/93e1238f1ef839e7ec5e71e03ec64ada1d7e8c52))
- call to `sort_params` ([0300b05](https://github.com/astroautomata/SymbolicRegression.jl/commit/0300b059b765b23c7eb92e12a681d0506165b464))
- ensure `operators` always available ([3225e6f](https://github.com/astroautomata/SymbolicRegression.jl/commit/3225e6f82cb319b3e452bfa99b63ec2749e6fbbe))
- guard more aliasing issues ([52f738a](https://github.com/astroautomata/SymbolicRegression.jl/commit/52f738adc2b62b040ea7ebf3e5a055fa1fe6b678))
- `AbstractOptions`6 for TemplateExpression ([8433d66](https://github.com/astroautomata/SymbolicRegression.jl/commit/8433d66df3ccc49f40cad21921f250a91f11979e))
- interaction with DispatchDoctor ([27746e4](https://github.com/astroautomata/SymbolicRegression.jl/commit/27746e4383606613b6a9b67d1bfd6e4ec83c1cec))
- make `AbstractOptions`8 into callable `AbstractOptions`9 ([8c91200](https://github.com/astroautomata/SymbolicRegression.jl/commit/8c912001864e7dfb2473b0170df4f2458f305033))
- method ambiguity ([1031d9b](https://github.com/astroautomata/SymbolicRegression.jl/commit/1031d9b51445828574035101776e4c1df02aa373))
- miscalculations of `AbstractOptions`2 ([686b844](https://github.com/astroautomata/SymbolicRegression.jl/commit/686b844debfb39a42ed3db919b7f04149d0726d1))
- missing calls to `AbstractRuntimeOptions`0 ([4e52ca4](https://github.com/astroautomata/SymbolicRegression.jl/commit/4e52ca4dc7b51b5b1093e77170480239e5d67281))
- missing import ([ae69e10](https://github.com/astroautomata/SymbolicRegression.jl/commit/ae69e104373ab49a07db616f68f89a36a6dfda3b))
- missing `AbstractOptions`0 ([f455f7a](https://github.com/astroautomata/SymbolicRegression.jl/commit/f455f7aebd519880510dfbf57da5abf0e30800ed))
- missing method for `AbstractRuntimeOptions`7 ([1d23cfb](https://github.com/astroautomata/SymbolicRegression.jl/commit/1d23cfb263b07033d4a5ad6a4bd500f9e6d0460f))
- MLJ saving unicode to csv ([f8ad354](https://github.com/astroautomata/SymbolicRegression.jl/commit/f8ad3542c8ad49e5fd24d8da93cd72a7adf274bf))
- new `AbstractOptions`5 miscalc ([bd6d8f5](https://github.com/astroautomata/SymbolicRegression.jl/commit/bd6d8f520f46b7efd5e1b463954ee10770a05732))
- new type instabilities from `AbstractRuntimeOptions`4 ([c809c6c](https://github.com/astroautomata/SymbolicRegression.jl/commit/c809c6cfea2735087682933ecdab9a0be2de751c))
- prevent aliasing during crossover ([a3d28ed](https://github.com/astroautomata/SymbolicRegression.jl/commit/a3d28ed00b0e880a314709255d6c6157d5298d7e))
- printing with explicit newline ([b62598f](https://github.com/astroautomata/SymbolicRegression.jl/commit/b62598f8b9fa3d8e2925a96173dff777d78e156d))
- put back constructorof ([aae35cb](https://github.com/astroautomata/SymbolicRegression.jl/commit/aae35cb11c581e043cd8758be5d508e7c8738cc5))
- re-enable precompilation ([e5c3427](https://github.com/astroautomata/SymbolicRegression.jl/commit/e5c342748b33bf9b28f2b65deb01cebd5ff21e9e))
- some bugs with ConstrainedExpression ([7223da3](https://github.com/astroautomata/SymbolicRegression.jl/commit/7223da30c415accf00c6d0caff116a3cfc00698a))
- some imports in ExpressionBuilder ([6c78145](https://github.com/astroautomata/SymbolicRegression.jl/commit/6c7814573daea7d0c65e5a03dcfa140ae9ac3109))
- type instability in annotated string ([e84f6ab](https://github.com/astroautomata/SymbolicRegression.jl/commit/e84f6ab9d03aec500d41b62de2dc7ace918b9342))
- type instability in eval_tree_array ([127241d](https://github.com/astroautomata/SymbolicRegression.jl/commit/127241d0de23264f8e5a4bda12e363554932bca5))
- type instability in `AbstractRuntimeOptions`3 ([1c809d1](https://github.com/astroautomata/SymbolicRegression.jl/commit/1c809d1149e110a59248d29a0e9d8d427b19f086))
- type instability in `AbstractMutationWeights`3 ([ede3f78](https://github.com/astroautomata/SymbolicRegression.jl/commit/ede3f7845effb84c1de3251af300c58823e7b6fe))
- type instability in ParametricExpression ([9c30d14](https://github.com/astroautomata/SymbolicRegression.jl/commit/9c30d141592bdcaf00db3dc740cf92987500033a))
- unbound type parameter ([2123ef2](https://github.com/astroautomata/SymbolicRegression.jl/commit/2123ef29c11aa5370a10da4040f63b256b122ff2))
- undo nonsensical change to compute complexity ([aab19ea](https://github.com/astroautomata/SymbolicRegression.jl/commit/aab19ea539383a802be650005b48bdc33e84c73e))
- update type inference utility for TemplateExpression ([97ea32b](https://github.com/astroautomata/SymbolicRegression.jl/commit/97ea32b1521aa4877f5af414f628a6211b512d56))
- weak dispatch in TemplateExpression ([acd7762](https://github.com/astroautomata/SymbolicRegression.jl/commit/acd7762c2a22a5f3a815b221ace0967b022a4ff6))

## [1.0.0-beta1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.24.5...v1.0.0-beta1) (2024-10-06)

### ⚠ BREAKING CHANGES

- change default for `rotate_tree`

### Features

- add classes feature to MLJ interface ([2f63ccb](https://github.com/astroautomata/SymbolicRegression.jl/commit/2f63ccb4b7e1b1097a015606c5ad6ed66a30fa76))
- add index parameter for Dataset ([11e30fb](https://github.com/astroautomata/SymbolicRegression.jl/commit/11e30fb683c3f057a20f794b29ff818157be37aa))
- add new string representations via dispatch ([ed684fc](https://github.com/astroautomata/SymbolicRegression.jl/commit/ed684fcb91820676780d1700bd7ccdb12e37c57a))
- add TODO item ([4fb7580](https://github.com/astroautomata/SymbolicRegression.jl/commit/4fb75804321b489483aee9da1d118a02bcc9920f))
- adjust sleep time to actual start of sleep ([c258c5d](https://github.com/astroautomata/SymbolicRegression.jl/commit/c258c5d9fb74babd88fdf34dce20c09f2ebc3c86))
- allow symbol for autodiff backend ([84e8161](https://github.com/astroautomata/SymbolicRegression.jl/commit/84e8161c71021a3b0ca47e912cf7db55a3653f1d))
- allow user-specified autodiff backend; finite or zygote ([ca43666](https://github.com/astroautomata/SymbolicRegression.jl/commit/ca43666cdb571e6d83226d0fb99e8a629b795800))
- avoid `Base.sleep` altogether ([0045774](https://github.com/astroautomata/SymbolicRegression.jl/commit/00457745672efe66ea9b4b63f3c893493b2c35f2))
- back to fast loss functions ([6a0e32a](https://github.com/astroautomata/SymbolicRegression.jl/commit/6a0e32a7073a1e4ea4e40b1090459c2f530720c7))
- better monitor of bottlenecks ([47da6f5](https://github.com/astroautomata/SymbolicRegression.jl/commit/47da6f5cf96633a16fb49c7d86bb5efcee0c90a5))
- better printing for halls of fame ([6a6ea78](https://github.com/astroautomata/SymbolicRegression.jl/commit/6a6ea787ce72347e1a95b5b9c9d66695a307bdbb))
- change default for `@threadcall`2 ([a622c09](https://github.com/astroautomata/SymbolicRegression.jl/commit/a622c0934043878a6d1e37237c419879de19405c))
- create `simplify_tree!`9 for efficient caching ([03624c4](https://github.com/astroautomata/SymbolicRegression.jl/commit/03624c4293944a4c563255d09ae0fc9048d24ae2))
- don't print worker occupation temporarily ([8e149bc](https://github.com/astroautomata/SymbolicRegression.jl/commit/8e149bc88197aa6a33db886ae763a619e06afc76))
- dont print occupation during warmup ([32fec18](https://github.com/astroautomata/SymbolicRegression.jl/commit/32fec189f983790a4707ab2284ccd58e642ebb22))
- enable tree rotation for unary operators ([06f4dab](https://github.com/astroautomata/SymbolicRegression.jl/commit/06f4dab2e53d527fde1a99f2f41c6c6bccbdd06b))
- Enzyme gradients for ParametricExpression ([54a38eb](https://github.com/astroautomata/SymbolicRegression.jl/commit/54a38eb218623efb9602f7e8752a4bad73ef6c69))
- explicit stack size for Enzyme ([0dac5c8](https://github.com/astroautomata/SymbolicRegression.jl/commit/0dac5c8555b228fe08975f0201c3656d78e5a473))
- export node_type ([6183296](https://github.com/astroautomata/SymbolicRegression.jl/commit/618329650d4b792bb629ccba6b90d35833c0e222))
- expose new `simplify_tree!`0 and `simplify_tree!`1 ([9204a1d](https://github.com/astroautomata/SymbolicRegression.jl/commit/9204a1d74cf7ba33eaa52e3cbab0242937306fbf))
- fallback to regular sleep if 1 thread ([62616e7](https://github.com/astroautomata/SymbolicRegression.jl/commit/62616e755d397816a691cf8dc327d5f488d93fb9))
- get Zygote gradients working for `ParametricExpressions` ([c3c2b53](https://github.com/astroautomata/SymbolicRegression.jl/commit/c3c2b53c16fccec57f7b85cdf02a3f82e790baa3))
- set node_type based on expression_type ([c7476d0](https://github.com/astroautomata/SymbolicRegression.jl/commit/c7476d07a6dd8e609cd98232eb98d48c48e22a17))
- set stack size to 32 MB for Enzyme ([e7b1340](https://github.com/astroautomata/SymbolicRegression.jl/commit/e7b1340f536b695a74e8f3f9cb1a35aad87698f6))
- undo abstract expression changes to InterfaceDynamicExpressions ([e06d982](https://github.com/astroautomata/SymbolicRegression.jl/commit/e06d982ccf37faa224618f08e7be12c3d50b1c63))
- use DifferentiationInterface.jl for AD backend ([fe9c603](https://github.com/astroautomata/SymbolicRegression.jl/commit/fe9c603d36e7d4a4bc2745bd275b94c6d08c5f53))
- use `@threadcall` for systemsleep ([40daf88](https://github.com/astroautomata/SymbolicRegression.jl/commit/40daf88becaba822b275e181918d93e660132a59))
- use `Threads.@spawn` over `@async` ([6b2464a](https://github.com/astroautomata/SymbolicRegression.jl/commit/6b2464af3b957303f8239c281d2dcd4a6fb753da))
- wip Enzyme support ([2190234](https://github.com/astroautomata/SymbolicRegression.jl/commit/2190234b24d053d731aa783134a6a5893ac4a639))
- working Enzyme gradients in loss function ([1577e67](https://github.com/astroautomata/SymbolicRegression.jl/commit/1577e671f48777c6b79d1fe5319c41d819593f5c))

### Bug Fixes

- all underscore identifier ([9bb4922](https://github.com/astroautomata/SymbolicRegression.jl/commit/9bb4922d7badeecd4c3e2a12ff591d6597fafe9b))
- ambiguities ([8fb0c94](https://github.com/astroautomata/SymbolicRegression.jl/commit/8fb0c948153e4197eadd2ae5ee4aac66a4545155))
- avoid storing `simplify_tree!`4 within `simplify_tree!`5 ([a4709bf](https://github.com/astroautomata/SymbolicRegression.jl/commit/a4709bf7496a0f04883fbe817110f7139aaf919c))
- consistency checks in metadata stripping ([37712f6](https://github.com/astroautomata/SymbolicRegression.jl/commit/37712f6d08906fd25a47d89a3303375fa177ee66))
- ensure `simplify_tree!`2 is copied for Enzyme analysis ([ffa9f52](https://github.com/astroautomata/SymbolicRegression.jl/commit/ffa9f52291d85eeeb656e60c3af43eedd8d53b60))
- ensure we continue in parametrized function test ([08f8d44](https://github.com/astroautomata/SymbolicRegression.jl/commit/08f8d4448a04c2e10b7600a374680797f0c92cd1))
- ensure we mark `simplify_tree!`6d argument as `simplify_tree!`7 ([1209652](https://github.com/astroautomata/SymbolicRegression.jl/commit/1209652c5a6b001196d357b993a9c962801861a0))
- EnzymeRules marking ([002df6d](https://github.com/astroautomata/SymbolicRegression.jl/commit/002df6d8b5d17e7fe85e8589df1dce6f942cf872))
- error message in rotation ([46921dc](https://github.com/astroautomata/SymbolicRegression.jl/commit/46921dc9d5c92095635f64dce607ec288ab7a30e))
- ignore functions in Enzyme and ChainRulesCore ([b4265c1](https://github.com/astroautomata/SymbolicRegression.jl/commit/b4265c17ca5cfcc3f91e482ebb9a03bc8e3e3985))
- `default_node -> default_node_type` ([13687b4](https://github.com/astroautomata/SymbolicRegression.jl/commit/13687b45c222faca295b8620d51cc0606f955bf4))
- issue with outer threads loop ([c12bac4](https://github.com/astroautomata/SymbolicRegression.jl/commit/c12bac41eb3af838cc39aefa1372eee675cd6535))
- issue with rotation of tree ([241f6dc](https://github.com/astroautomata/SymbolicRegression.jl/commit/241f6dc737fb9aed870e092272a512378c10c0e1))
- jet issues with union splitting ([8d50d4d](https://github.com/astroautomata/SymbolicRegression.jl/commit/8d50d4d62522796360004af5834108f224d56019))
- jet union split ([381b3a7](https://github.com/astroautomata/SymbolicRegression.jl/commit/381b3a77c02e80b7ec86d1a0ab992ae82128a331))
- mistaken assertion ([dae5593](https://github.com/astroautomata/SymbolicRegression.jl/commit/dae559392d6f983e9e6d77f0178dce663067e017))
- mlj interface for classes ([05493f6](https://github.com/astroautomata/SymbolicRegression.jl/commit/05493f6a3f0f957f94de94a86ba0d383337a8e3c))
- more type stability for Enzyme ([1d60c81](https://github.com/astroautomata/SymbolicRegression.jl/commit/1d60c818cda31c8f08f8e3c2ffce3d9fc594f8df))
- move back to `@async` to fix race condition ([86a39f0](https://github.com/astroautomata/SymbolicRegression.jl/commit/86a39f0a3e4b4ff8d6480eefc11eb7964c4d6a26))
- nonblocking sleep ([e6f29d8](https://github.com/astroautomata/SymbolicRegression.jl/commit/e6f29d84525c12c1e6d005db72ebde038d4a9bc9))
- order of ParametricExpression arguments ([6c9b9e9](https://github.com/astroautomata/SymbolicRegression.jl/commit/6c9b9e9e908861d1b0e36c7229f0b046fcce1266))
- prevent bad RNGs in MLJ tests ([5ab8d16](https://github.com/astroautomata/SymbolicRegression.jl/commit/5ab8d16f7e12195af2945872dce398b113f141c5))
- repeated depwarns cause dict write error ([bb3846d](https://github.com/astroautomata/SymbolicRegression.jl/commit/bb3846de859b98f69927565039a907fec4ce823c))
- simplification within SingleIteration ([4d5f1cc](https://github.com/astroautomata/SymbolicRegression.jl/commit/4d5f1cc7460f94563df6981c7d9e6d79d4d63c47))
- stripping of metadata in loaded state ([38923b7](https://github.com/astroautomata/SymbolicRegression.jl/commit/38923b75c776259ba09374cace2902e7d5295182))
- switch out julia sleep implementation ([5a09dea](https://github.com/astroautomata/SymbolicRegression.jl/commit/5a09dea64097aa15324c845687b40a769469e441))
- type instability in `init_dummy_pops` ([80fb38f](https://github.com/astroautomata/SymbolicRegression.jl/commit/80fb38fbfb588be70e6e06485903f40973c9b29d))
- use of `simplify_tree!` ([d1d8e41](https://github.com/astroautomata/SymbolicRegression.jl/commit/d1d8e4187a8656e70326a61271fdc627c85617d5))
- various method ambiguities ([4bd4658](https://github.com/astroautomata/SymbolicRegression.jl/commit/4bd46586b96ea069a611316831e3c292aea84ffe))
- when bin constraints passed as dict ([e078916](https://github.com/astroautomata/SymbolicRegression.jl/commit/e078916799d3d0ce690b47f735ba1489e02f0ac1))

### Reverts

- change to `@threadcall` ([e899d58](https://github.com/astroautomata/SymbolicRegression.jl/commit/e899d589b8a2b414ab70c43fbfb0be49ea6432c3))

## [0.24.5](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.24.4...v0.24.5) (2024-06-16)

### Features

- allow vector of variable complexities ([e5f2d3e](https://github.com/astroautomata/SymbolicRegression.jl/commit/e5f2d3e12a506afc0f0c981700f6bc317aef280a))

### Bug Fixes

- allow for scalar variable complexities ([9553c52](https://github.com/astroautomata/SymbolicRegression.jl/commit/9553c5212e7231418c3d87d0f85d20ae1b3e3599))
- mark more functions as unstable ([4a6dc8a](https://github.com/astroautomata/SymbolicRegression.jl/commit/4a6dc8a2176d94633f411dbe1f02a47ff5f43c89))
- some type instabilities ([065a4f9](https://github.com/astroautomata/SymbolicRegression.jl/commit/065a4f9d687c649efc9de19e15042d207959ce37))
- various issues found by JET ([5d5d6dc](https://github.com/astroautomata/SymbolicRegression.jl/commit/5d5d6dc4ea3b00b3de3f4946779cd398cc2ac709))

## [0.24.4](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.24.3...v0.24.4) (2024-04-28)

### Features

- add option to force dimensionless constants ([571f85b](https://github.com/astroautomata/SymbolicRegression.jl/commit/571f85bd6df45629660608802462bdb7d757d89e))
- use `?` for wildcard units instead of cdot ([df86692](https://github.com/astroautomata/SymbolicRegression.jl/commit/df8669233aaf77f5cd084dc6bba60504656ec70e))

## [0.24.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.24.2...v0.24.3) (2024-04-26)

### Bug Fixes

- add missing `nout` in save_to_file ([606a7f8](https://github.com/astroautomata/SymbolicRegression.jl/commit/606a7f8a757b0a3aae9827d2355b8f3bf201b970))
- avoid parallelism on deterministic mode ([1babc81](https://github.com/astroautomata/SymbolicRegression.jl/commit/1babc81758fa24e8d46f0cb62bf9a951c491f3cf))

## [0.24.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.24.1...v0.24.2) (2024-04-14)

### Bug Fixes

- distributed extensions on 1.11 ([8693249](https://github.com/astroautomata/SymbolicRegression.jl/commit/8693249a8309eafc688e112f65e1f4ac12e42122))
- eval on `Core.Main` not `MainInclude` ([01fc984](https://github.com/astroautomata/SymbolicRegression.jl/commit/01fc9843f4b1b1729e65c7598ac0ee1589508e7d))

## [0.24.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.24.0...v0.24.1) (2024-03-24)

## [0.24.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.23.3...v0.24.0) (2024-03-20)

## [0.23.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.23.2...v0.23.3) (2024-02-23)

## [0.23.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.23.1...v0.23.2) (2024-02-17)

## [0.23.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.23.0...v0.23.1) (2024-01-03)

## [0.23.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.22.5...v0.23.0) (2023-12-24)

## [0.22.5](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.22.4...v0.22.5) (2023-12-11)

## [0.22.4](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.22.3...v0.22.4) (2023-08-20)

## [0.22.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.22.2...v0.22.3) (2023-08-17)

## [0.22.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.22.1...v0.22.2) (2023-08-10)

## [0.22.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.22.0...v0.22.1) (2023-08-07)

## [0.22.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.21.5...v0.22.0) (2023-08-07)

## [0.21.5](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.21.4...v0.21.5) (2023-08-02)

## [0.21.4](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.21.3...v0.21.4) (2023-08-01)

## [0.21.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.21.2...v0.21.3) (2023-07-27)

## [0.21.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.21.1...v0.21.2) (2023-07-23)

## [0.21.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.21.0...v0.21.1) (2023-07-22)

## [0.21.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.20.0...v0.21.0) (2023-07-22)

## [0.20.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.19.1...v0.20.0) (2023-07-05)

## [0.19.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.19.0...v0.19.1) (2023-06-19)

## [0.19.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.18.0...v0.19.0) (2023-05-28)

## [0.18.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.17.1...v0.18.0) (2023-05-12)

## [0.17.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.17.0...v0.17.1) (2023-04-26)

## [0.17.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.16.3...v0.17.0) (2023-04-22)

## [0.16.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.16.2...v0.16.3) (2023-04-13)

## [0.16.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.16.1...v0.16.2) (2023-03-25)

## [0.16.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.16.0...v0.16.1) (2023-03-21)

## [0.16.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.15.3...v0.16.0) (2023-03-20)

## [0.15.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.15.2...v0.15.3) (2023-03-03)

## [0.15.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.15.1...v0.15.2) (2023-02-18)

## [0.15.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.15.0...v0.15.1) (2023-02-13)

## [0.15.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.14.5...v0.15.0) (2023-01-16)

## [0.14.5](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.14.4...v0.14.5) (2022-11-28)

## [0.14.4](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.14.3...v0.14.4) (2022-11-21)

## [0.14.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.14.2...v0.14.3) (2022-11-04)

## [0.14.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.14.1...v0.14.2) (2022-11-03)

## [0.14.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.14.0...v0.14.1) (2022-11-03)

## [0.14.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.13.3...v0.14.0) (2022-10-31)

## [0.13.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.13.2...v0.13.3) (2022-10-31)

## [0.13.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.13.1...v0.13.2) (2022-10-24)

## [0.13.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.13.0...v0.13.1) (2022-10-24)

## [0.13.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.12.6...v0.13.0) (2022-10-24)

## [0.12.6](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.12.5...v0.12.6) (2022-10-22)

## [0.12.5](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.12.4...v0.12.5) (2022-10-18)

## [0.12.4](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.12.3...v0.12.4) (2022-10-17)

## [0.12.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.12.2...v0.12.3) (2022-10-14)

## [0.12.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.12.1...v0.12.2) (2022-10-06)

## [0.12.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.12.0...v0.12.1) (2022-09-10)

## [0.12.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.11.1...v0.12.0) (2022-09-10)

## [0.11.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.10.2...v0.11.1) (2022-09-09)

## [0.10.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.9.7...v0.10.2) (2022-08-22)

## [0.9.7](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.9.6...v0.9.7) (2022-07-08)

## [0.9.6](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.9.5...v0.9.6) (2022-06-03)

## [0.9.5](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.9.3...v0.9.5) (2022-06-02)

## [0.9.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.9.2...v0.9.3) (2022-05-23)

## [0.9.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.9.0...v0.9.2) (2022-05-16)

## [0.9.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.8.7...v0.9.0) (2022-05-02)

## [0.8.7](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.8.6...v0.8.7) (2022-04-25)

## [0.8.6](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.8.5...v0.8.6) (2022-04-24)

## [0.8.5](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.8.3...v0.8.5) (2022-04-23)

## [0.8.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.8.2...v0.8.3) (2022-04-10)

## [0.8.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.8.1...v0.8.2) (2022-04-08)

## [0.8.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.7.13...v0.8.1) (2022-03-28)

## [0.7.13](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.7.10...v0.7.13) (2022-02-23)

## [0.7.10](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.7.9...v0.7.10) (2022-02-14)

## [0.7.9](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.7.8...v0.7.9) (2022-02-14)

## [0.7.8](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.7.7...v0.7.8) (2022-02-12)

## [0.7.7](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.7.6...v0.7.7) (2022-02-02)

## [0.7.6](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.7.5...v0.7.6) (2022-02-02)

## [0.7.5](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.7.4...v0.7.5) (2022-02-01)

## [0.7.4](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.7.3...v0.7.4) (2022-02-01)

## [0.7.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.7.2...v0.7.3) (2022-02-01)

## [0.7.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.7.1...v0.7.2) (2022-01-31)

## [0.7.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.7.0...v0.7.1) (2022-01-31)

## [0.7.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.6.19...v0.7.0) (2022-01-24)

## [0.6.19](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.6.18...v0.6.19) (2022-01-22)

## [0.6.18](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.6.17...v0.6.18) (2022-01-18)

## [0.6.17](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.6.16...v0.6.17) (2022-01-18)

## [0.6.16](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.6.15...v0.6.16) (2021-11-11)

## [0.6.15](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.6.14...v0.6.15) (2021-11-08)

## [0.6.14](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.6.13...v0.6.14) (2021-09-21)

## [0.6.13](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.6.12...v0.6.13) (2021-09-14)

## [0.6.12](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.6.11...v0.6.12) (2021-08-04)

## [0.6.11](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.6.10...v0.6.11) (2021-07-09)

## [0.6.10](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.6.9...v0.6.10) (2021-07-08)

## [0.6.9](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.6.8...v0.6.9) (2021-06-16)

## [0.6.8](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.6.7...v0.6.8) (2021-06-15)

## [0.6.7](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.6.6...v0.6.7) (2021-06-14)

## [0.6.6](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.6.5...v0.6.6) (2021-06-14)

## [0.6.5](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.6.4...v0.6.5) (2021-06-08)

## [0.6.4](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.6.3...v0.6.4) (2021-06-06)

## [0.6.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.6.2...v0.6.3) (2021-06-06)

## [0.6.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.6.1...v0.6.2) (2021-06-04)

## [0.6.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.6.0...v0.6.1) (2021-06-02)

## [0.6.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.5.16...v0.6.0) (2021-05-30)

## [0.5.16](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.5.15...v0.5.16) (2021-03-06)

## [0.5.15](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.5.14...v0.5.15) (2021-03-06)

## [0.5.14](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.5.13...v0.5.14) (2021-03-06)

## [0.5.13](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.5.12...v0.5.13) (2021-03-01)

## [0.5.12](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.5.11...v0.5.12) (2021-02-26)

## [0.5.11](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.5.10...v0.5.11) (2021-02-26)

## [0.5.10](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.5.9...v0.5.10) (2021-02-26)

## [0.5.9](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.5.8...v0.5.9) (2021-02-25)

## [0.5.8](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.5.7...v0.5.8) (2021-02-25)

## [0.5.7](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.5.6...v0.5.7) (2021-02-25)

## [0.5.6](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.5.5...v0.5.6) (2021-02-25)

## [0.5.5](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.5.4...v0.5.5) (2021-02-25)

## [0.5.4](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.5.3...v0.5.4) (2021-02-25)

## [0.5.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.5.2...v0.5.3) (2021-02-25)

## [0.5.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.5.1...v0.5.2) (2021-02-24)

## [0.5.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.5.0...v0.5.1) (2021-02-24)

## [0.5.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.4.11...v0.5.0) (2021-02-11)

## [0.4.11](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.4.10...v0.4.11) (2021-02-09)

## [0.4.10](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.4.9...v0.4.10) (2021-02-09)

## [0.4.9](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.4.8...v0.4.9) (2021-02-08)

## [0.4.8](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.4.7...v0.4.8) (2021-02-08)

## [0.4.7](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.4.6...v0.4.7) (2021-02-05)

## [0.4.6](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.4.5...v0.4.6) (2021-02-04)

## [0.4.5](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.4.4...v0.4.5) (2021-02-04)

## [0.4.4](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.4.3...v0.4.4) (2021-02-04)

## [0.4.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.4.2...v0.4.3) (2021-02-03)

## [0.4.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.4.1...v0.4.2) (2021-02-03)

## [0.4.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.4.0...v0.4.1) (2021-02-02)

## [0.4.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.3.5...v0.4.0) (2021-02-01)

## [0.3.5](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.3.4...v0.3.5) (2021-02-01)

## [0.3.4](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.3.3...v0.3.4) (2021-01-31)

## [0.3.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.3.2...v0.3.3) (2021-01-30)

## [0.3.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.3.1...v0.3.2) (2021-01-29)

## [0.3.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.3.0...v0.3.1) (2021-01-29)

## [0.3.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.2.2...v0.3.0) (2021-01-29)

## [0.2.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.2.1...v0.2.2) (2021-01-29)

## [0.2.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.2.0...v0.2.1) (2021-01-29)

## [0.2.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v0.1.0...v0.2.0) (2026-02-14)

## 0.1.0 (2026-02-14)

### Bug Fixes

- 10 issue with hall of fame not saving ([c9adc43](https://github.com/astroautomata/SymbolicRegression.jl/commit/c9adc43d8dd7ac54579b9d1249fe3f71a385c161))
