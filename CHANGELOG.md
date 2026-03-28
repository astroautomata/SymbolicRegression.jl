<!-- markdownlint-disable MD033 -->
<!-- markdownlint-disable MD034 -->
<!-- markdownlint-disable MD024 -->

# Changelog

## [1.13.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.13.1...v1.13.2) (2026-03-28)

### Bug Fixes

- enforce constraints in hall-of-fame (backport) ([#593](https://github.com/astroautomata/SymbolicRegression.jl/issues/593)) ([cc7e4c0](https://github.com/astroautomata/SymbolicRegression.jl/commit/cc7e4c09dd3152ea91089b0bdd8c2140254c05b5))

## [1.13.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.13.0...v1.13.1) (2026-03-23)

### Bug Fixes

- use eltype(x0) instead of T for randn in constant optimization (backport to release-v1) ([#571](https://github.com/astroautomata/SymbolicRegression.jl/issues/571)) ([13ca9c4](https://github.com/astroautomata/SymbolicRegression.jl/commit/13ca9c4bfad9b50ef4c7e88961f1a736bc979c98))

## [1.13.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.12.1...v1.13.0) (2026-03-09)

### Bug Fixes

- clean up output of errormonitor ([#555](https://github.com/astroautomata/SymbolicRegression.jl/issues/555)) ([210deac](https://github.com/astroautomata/SymbolicRegression.jl/commit/210deacdaf253777c3041c4749eac1898d555083))

## [1.12.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.12.0...v1.12.1) (2026-02-14)

## [1.12.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.11.3...v1.12.0) (2025-06-24)

### Bug Fixes

- issue where minimizer is not loaded to tree ([f0ff1a0](https://github.com/astroautomata/SymbolicRegression.jl/commit/f0ff1a01e48a30b19effe6d610dd571f9ed4dfd0))
- issue where minimizer is not loaded to tree ([8b05c9f](https://github.com/astroautomata/SymbolicRegression.jl/commit/8b05c9fdbdce740f43db06ab9d75e95335cfcd5b))

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
- allow `@template_spec` to declare explicit num_features ([b24f707](https://github.com/astroautomata/SymbolicRegression.jl/commit/b24f70762ddb6a8804cc49bed6b35719c6600329))
- allow negative losses ([fc9fcdb](https://github.com/astroautomata/SymbolicRegression.jl/commit/fc9fcdbfac515efe2b53e1af0ee7f7cdeb23986a))
- allow negative losses ([2f38af9](https://github.com/astroautomata/SymbolicRegression.jl/commit/2f38af9ed20ed1090adeb4a45e3a6633538b83f2))
- avoid use of scores when assuming negative losses ([996d930](https://github.com/astroautomata/SymbolicRegression.jl/commit/996d93097b447a379873be72484b78e2d1d5aff8))
- move `get_options` into top namespace ([3726466](https://github.com/astroautomata/SymbolicRegression.jl/commit/37264668adcb06279ea23f203ca91bcf99d4caae))
- recommend users use TemplateExpressionSpec instead ([ad07294](https://github.com/astroautomata/SymbolicRegression.jl/commit/ad072940ad2deb9c9b588645b2cf6e44e0fab664))

### Bug Fixes

- avoid printing heap size hint if already created ([4334193](https://github.com/astroautomata/SymbolicRegression.jl/commit/43341939ad9b1224de60254dfc1e7c3bfe7cb321))
- avoid printing heap size hint if already created ([64c0780](https://github.com/astroautomata/SymbolicRegression.jl/commit/64c0780d268f13a0a0e54615d273ffbb123170de))
- Enzyme extension (up to issues of Enzyme itself) ([8f32e96](https://github.com/astroautomata/SymbolicRegression.jl/commit/8f32e9689c823a61277b19224b789a7c59ce2090))
- per task cache can be immutable ([2a8663c](https://github.com/astroautomata/SymbolicRegression.jl/commit/2a8663c0040baf1fe394fd54b6c725fda6e08768))
- per task cache can be immutable ([7708ff9](https://github.com/astroautomata/SymbolicRegression.jl/commit/7708ff969293189b6c25d059f76029a3edd2d491))
- scope error in hall of fame formatting ([64c994d](https://github.com/astroautomata/SymbolicRegression.jl/commit/64c994d9c4f9569882a0c24fb7259c077e5696f7))

## [1.10.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.9.3...v1.10.0) (2025-05-01)

### Features

- allow `Any` for input types ([07dbceb](https://github.com/astroautomata/SymbolicRegression.jl/commit/07dbceb489f65a5779afbe0b0439648296826fef))
- finish remaining parts of string interface ([247f533](https://github.com/astroautomata/SymbolicRegression.jl/commit/247f53316f4fe4cd88eb2314b44c38dfe194c738))
- initial compat with string features ([008cdc1](https://github.com/astroautomata/SymbolicRegression.jl/commit/008cdc19d327424c419921f74024ed8e2f8672ed))

## [1.9.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.9.2...v1.9.3) (2025-04-25)

### Bug Fixes

- unary constraint check missed ([bfbb254](https://github.com/astroautomata/SymbolicRegression.jl/commit/bfbb2546128bb2704ff08770d58443c8fa79007c))
- unary constraint check missed ([f08f76d](https://github.com/astroautomata/SymbolicRegression.jl/commit/f08f76d309917ed50946272d6e09621f9adc8681))

## [1.9.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.9.1...v1.9.2) (2025-04-10)

## [1.9.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.9.0...v1.9.1) (2025-04-04)

## [1.9.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.8.0...v1.9.0) (2025-03-01)

### Bug Fixes

- printing greater and lesser ([d5f6fbd](https://github.com/astroautomata/SymbolicRegression.jl/commit/d5f6fbd1aacd1a5fe7dc9c6729d6dacf29b61830))
- printing greater and lesser ([3a85b69](https://github.com/astroautomata/SymbolicRegression.jl/commit/3a85b69659e387383f3210960460e4557eb259a8))

## [1.8.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.7.2...v1.8.0) (2025-02-22)

### Features

- allow recording crossovers ([#415](https://github.com/astroautomata/SymbolicRegression.jl/issues/415)) ([23a4f2e](https://github.com/astroautomata/SymbolicRegression.jl/commit/23a4f2e7dbd86b6ab1f5f7c71d519ec16b906840))
- better error for mismatched eltypes ([68d6397](https://github.com/astroautomata/SymbolicRegression.jl/commit/68d63978d414940a9c492bd1b75471173120fe1e))
- better error for mismatched eltypes ([d70fe09](https://github.com/astroautomata/SymbolicRegression.jl/commit/d70fe09d38864b4f2b2ecdf6d17c7b7a8bcaf9b4))
- explicitly monitor errors in workers ([b86b4c1](https://github.com/astroautomata/SymbolicRegression.jl/commit/b86b4c1ed37328b83635d2f5fa7d826d84092c7a))
- explicitly monitor errors in workers ([28eb285](https://github.com/astroautomata/SymbolicRegression.jl/commit/28eb28503fd13b36f7dea98657ccd6cb1247caba))
- generic getters for datasets ([3b923bd](https://github.com/astroautomata/SymbolicRegression.jl/commit/3b923bd65a7bd16d629a054f07e3e680e4da1022))
- utility functions for batching dataset ([bb406ed](https://github.com/astroautomata/SymbolicRegression.jl/commit/bb406edb0c137bbcca3cefcb64d0d02b5406b38e))

### Bug Fixes

- batched dataset for optimisation ([d085fd8](https://github.com/astroautomata/SymbolicRegression.jl/commit/d085fd837e323d82bf363f4e8f986bd6ab5fb5f9))
- batched dataset for optimisation ([5629410](https://github.com/astroautomata/SymbolicRegression.jl/commit/562941040d95f6154d41ddde8ec4d5e5ee57fbff))
- only optimize hall of fame if exists ([cc3a8a5](https://github.com/astroautomata/SymbolicRegression.jl/commit/cc3a8a52b3f6e90fc847e4bebd2694a143455f95))
- parametric expressions batching ([2d6f665](https://github.com/astroautomata/SymbolicRegression.jl/commit/2d6f665bc327f6a1ee5a9c9d04b48c99afcc17e7))

## [1.7.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.7.1...v1.7.2) (2025-02-13)

### Bug Fixes

- max of 6 expressions bug ([fcb03d9](https://github.com/astroautomata/SymbolicRegression.jl/commit/fcb03d9c9692df5d8e756d35653f3206c1a914a1))
- max of 6 expressions bug ([1badff4](https://github.com/astroautomata/SymbolicRegression.jl/commit/1badff4e6f7f1b58bd42ca88b21cbd4eab357d9f))

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
- overload additional operations for ComposableExpression ([288824d](https://github.com/astroautomata/SymbolicRegression.jl/commit/288824def89a95710931c5e775271f2642637b10))
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
- allow for variable `nthreads` ([9fabc30](https://github.com/astroautomata/SymbolicRegression.jl/commit/9fabc303dd33c624739e759d960374c7f85e56f7))

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

- add `literal_pow` for composable expression ([2cd4c1a](https://github.com/astroautomata/SymbolicRegression.jl/commit/2cd4c1a6dd37c8011184f569ac2ab75fb1aadf54))
- add missing `literal_pow` ([2a92af1](https://github.com/astroautomata/SymbolicRegression.jl/commit/2a92af1464c80edcf68b7fd8bc769deed545296d))
- higher order safe operators ([12449ca](https://github.com/astroautomata/SymbolicRegression.jl/commit/12449ca4451fbd3867063a81d4f25c83f90b37ba))
- higher order safe operators ([5dbd23a](https://github.com/astroautomata/SymbolicRegression.jl/commit/5dbd23abd698412de59b3a08f7889ea09bcf5345))
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
- allow user-specified `stdin` ([1fc4611](https://github.com/astroautomata/SymbolicRegression.jl/commit/1fc461168efb46aad98babe764132a1d25f03a30))
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
- add missing `condition_mutation_weights!` to fix [#378](https://github.com/astroautomata/SymbolicRegression.jl/issues/378) ([3565421](https://github.com/astroautomata/SymbolicRegression.jl/commit/35654219dbca65aef75609c918e7722675a73734))

## [1.1.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.0.3...v1.1.0) (2024-12-03)

### Features

- allow passing additional extensions for worker imports ([788ce37](https://github.com/astroautomata/SymbolicRegression.jl/commit/788ce37f48c9106a95c2158be3aa137a0cea8bca))

### Bug Fixes

- distributed TensorBoardLogging ([272195e](https://github.com/astroautomata/SymbolicRegression.jl/commit/272195e8057693d4908800c66ed5c7f1d8c11548))

## [1.0.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.0.2...v1.0.3) (2024-11-28)

### Features

- allow argument-less TemplateExpression parts ([f4c0d7c](https://github.com/astroautomata/SymbolicRegression.jl/commit/f4c0d7c51b83fa52d39be23f5359db93c126bc44))
- allow argument-less TemplateExpression parts ([6d2a72d](https://github.com/astroautomata/SymbolicRegression.jl/commit/6d2a72d0d42d5aeda4c3f9b75231319cef420575))

### Bug Fixes

- `predict` for TemplateExpressions ([808bd10](https://github.com/astroautomata/SymbolicRegression.jl/commit/808bd10111a1232ec722f1f6a89ffb7a4417bb68))
- `predict` for TemplateExpressions ([3f4b201](https://github.com/astroautomata/SymbolicRegression.jl/commit/3f4b201254e5a80af67843d2e997aa6ec1227506))

## [1.0.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.0.1...v1.0.2) (2024-11-24)

### Bug Fixes

- widen type constraints for TemplateExpression ([b5fc8eb](https://github.com/astroautomata/SymbolicRegression.jl/commit/b5fc8eb63bbd48444266c6dcb862c88ead7717db))
- widen type constraints for TemplateExpression evaluation ([dedb41a](https://github.com/astroautomata/SymbolicRegression.jl/commit/dedb41a6b7c40f97e74d361046d34717d83f2fb9))

## [1.0.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.0.0...v1.0.1) (2024-11-20)

## [1.13.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.12.1...v1.13.0) (2026-03-09)

### Bug Fixes

- clean up output of errormonitor ([#555](https://github.com/astroautomata/SymbolicRegression.jl/issues/555)) ([210deac](https://github.com/astroautomata/SymbolicRegression.jl/commit/210deacdaf253777c3041c4749eac1898d555083))

## [1.12.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.12.0...v1.12.1) (2026-02-14)

## [1.12.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.11.3...v1.12.0) (2025-06-24)

### Bug Fixes

- issue where minimizer is not loaded to tree ([f0ff1a0](https://github.com/astroautomata/SymbolicRegression.jl/commit/f0ff1a01e48a30b19effe6d610dd571f9ed4dfd0))
- issue where minimizer is not loaded to tree ([8b05c9f](https://github.com/astroautomata/SymbolicRegression.jl/commit/8b05c9fdbdce740f43db06ab9d75e95335cfcd5b))

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
- allow `@template_spec` to declare explicit num_features ([b24f707](https://github.com/astroautomata/SymbolicRegression.jl/commit/b24f70762ddb6a8804cc49bed6b35719c6600329))
- allow negative losses ([fc9fcdb](https://github.com/astroautomata/SymbolicRegression.jl/commit/fc9fcdbfac515efe2b53e1af0ee7f7cdeb23986a))
- allow negative losses ([2f38af9](https://github.com/astroautomata/SymbolicRegression.jl/commit/2f38af9ed20ed1090adeb4a45e3a6633538b83f2))
- avoid use of scores when assuming negative losses ([996d930](https://github.com/astroautomata/SymbolicRegression.jl/commit/996d93097b447a379873be72484b78e2d1d5aff8))
- move `get_options` into top namespace ([3726466](https://github.com/astroautomata/SymbolicRegression.jl/commit/37264668adcb06279ea23f203ca91bcf99d4caae))
- recommend users use TemplateExpressionSpec instead ([ad07294](https://github.com/astroautomata/SymbolicRegression.jl/commit/ad072940ad2deb9c9b588645b2cf6e44e0fab664))

### Bug Fixes

- avoid printing heap size hint if already created ([4334193](https://github.com/astroautomata/SymbolicRegression.jl/commit/43341939ad9b1224de60254dfc1e7c3bfe7cb321))
- avoid printing heap size hint if already created ([64c0780](https://github.com/astroautomata/SymbolicRegression.jl/commit/64c0780d268f13a0a0e54615d273ffbb123170de))
- Enzyme extension (up to issues of Enzyme itself) ([8f32e96](https://github.com/astroautomata/SymbolicRegression.jl/commit/8f32e9689c823a61277b19224b789a7c59ce2090))
- per task cache can be immutable ([2a8663c](https://github.com/astroautomata/SymbolicRegression.jl/commit/2a8663c0040baf1fe394fd54b6c725fda6e08768))
- per task cache can be immutable ([7708ff9](https://github.com/astroautomata/SymbolicRegression.jl/commit/7708ff969293189b6c25d059f76029a3edd2d491))
- scope error in hall of fame formatting ([64c994d](https://github.com/astroautomata/SymbolicRegression.jl/commit/64c994d9c4f9569882a0c24fb7259c077e5696f7))

## [1.10.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.9.3...v1.10.0) (2025-05-01)

### Features

- allow `Any` for input types ([07dbceb](https://github.com/astroautomata/SymbolicRegression.jl/commit/07dbceb489f65a5779afbe0b0439648296826fef))
- finish remaining parts of string interface ([247f533](https://github.com/astroautomata/SymbolicRegression.jl/commit/247f53316f4fe4cd88eb2314b44c38dfe194c738))
- initial compat with string features ([008cdc1](https://github.com/astroautomata/SymbolicRegression.jl/commit/008cdc19d327424c419921f74024ed8e2f8672ed))

## [1.9.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.9.2...v1.9.3) (2025-04-25)

### Bug Fixes

- unary constraint check missed ([bfbb254](https://github.com/astroautomata/SymbolicRegression.jl/commit/bfbb2546128bb2704ff08770d58443c8fa79007c))
- unary constraint check missed ([f08f76d](https://github.com/astroautomata/SymbolicRegression.jl/commit/f08f76d309917ed50946272d6e09621f9adc8681))

## [1.9.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.9.1...v1.9.2) (2025-04-10)

## [1.9.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.9.0...v1.9.1) (2025-04-04)

## [1.9.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.8.0...v1.9.0) (2025-03-01)

### Bug Fixes

- printing greater and lesser ([d5f6fbd](https://github.com/astroautomata/SymbolicRegression.jl/commit/d5f6fbd1aacd1a5fe7dc9c6729d6dacf29b61830))
- printing greater and lesser ([3a85b69](https://github.com/astroautomata/SymbolicRegression.jl/commit/3a85b69659e387383f3210960460e4557eb259a8))

## [1.8.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.7.2...v1.8.0) (2025-02-22)

### Features

- allow recording crossovers ([#415](https://github.com/astroautomata/SymbolicRegression.jl/issues/415)) ([23a4f2e](https://github.com/astroautomata/SymbolicRegression.jl/commit/23a4f2e7dbd86b6ab1f5f7c71d519ec16b906840))
- better error for mismatched eltypes ([68d6397](https://github.com/astroautomata/SymbolicRegression.jl/commit/68d63978d414940a9c492bd1b75471173120fe1e))
- better error for mismatched eltypes ([d70fe09](https://github.com/astroautomata/SymbolicRegression.jl/commit/d70fe09d38864b4f2b2ecdf6d17c7b7a8bcaf9b4))
- explicitly monitor errors in workers ([b86b4c1](https://github.com/astroautomata/SymbolicRegression.jl/commit/b86b4c1ed37328b83635d2f5fa7d826d84092c7a))
- explicitly monitor errors in workers ([28eb285](https://github.com/astroautomata/SymbolicRegression.jl/commit/28eb28503fd13b36f7dea98657ccd6cb1247caba))
- generic getters for datasets ([3b923bd](https://github.com/astroautomata/SymbolicRegression.jl/commit/3b923bd65a7bd16d629a054f07e3e680e4da1022))
- utility functions for batching dataset ([bb406ed](https://github.com/astroautomata/SymbolicRegression.jl/commit/bb406edb0c137bbcca3cefcb64d0d02b5406b38e))

### Bug Fixes

- batched dataset for optimisation ([d085fd8](https://github.com/astroautomata/SymbolicRegression.jl/commit/d085fd837e323d82bf363f4e8f986bd6ab5fb5f9))
- batched dataset for optimisation ([5629410](https://github.com/astroautomata/SymbolicRegression.jl/commit/562941040d95f6154d41ddde8ec4d5e5ee57fbff))
- only optimize hall of fame if exists ([cc3a8a5](https://github.com/astroautomata/SymbolicRegression.jl/commit/cc3a8a52b3f6e90fc847e4bebd2694a143455f95))
- parametric expressions batching ([2d6f665](https://github.com/astroautomata/SymbolicRegression.jl/commit/2d6f665bc327f6a1ee5a9c9d04b48c99afcc17e7))

## [1.7.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.7.1...v1.7.2) (2025-02-13)

### Bug Fixes

- max of 6 expressions bug ([fcb03d9](https://github.com/astroautomata/SymbolicRegression.jl/commit/fcb03d9c9692df5d8e756d35653f3206c1a914a1))
- max of 6 expressions bug ([1badff4](https://github.com/astroautomata/SymbolicRegression.jl/commit/1badff4e6f7f1b58bd42ca88b21cbd4eab357d9f))

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
- overload additional operations for ComposableExpression ([288824d](https://github.com/astroautomata/SymbolicRegression.jl/commit/288824def89a95710931c5e775271f2642637b10))
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
- allow for variable `nthreads` ([9fabc30](https://github.com/astroautomata/SymbolicRegression.jl/commit/9fabc303dd33c624739e759d960374c7f85e56f7))

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

- add `literal_pow` for composable expression ([2cd4c1a](https://github.com/astroautomata/SymbolicRegression.jl/commit/2cd4c1a6dd37c8011184f569ac2ab75fb1aadf54))
- add missing `literal_pow` ([2a92af1](https://github.com/astroautomata/SymbolicRegression.jl/commit/2a92af1464c80edcf68b7fd8bc769deed545296d))
- higher order safe operators ([12449ca](https://github.com/astroautomata/SymbolicRegression.jl/commit/12449ca4451fbd3867063a81d4f25c83f90b37ba))
- higher order safe operators ([5dbd23a](https://github.com/astroautomata/SymbolicRegression.jl/commit/5dbd23abd698412de59b3a08f7889ea09bcf5345))
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
- allow user-specified `stdin` ([1fc4611](https://github.com/astroautomata/SymbolicRegression.jl/commit/1fc461168efb46aad98babe764132a1d25f03a30))
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
- add missing `condition_mutation_weights!` to fix [#378](https://github.com/astroautomata/SymbolicRegression.jl/issues/378) ([3565421](https://github.com/astroautomata/SymbolicRegression.jl/commit/35654219dbca65aef75609c918e7722675a73734))

## [1.1.0](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.0.3...v1.1.0) (2024-12-03)

### Features

- allow passing additional extensions for worker imports ([788ce37](https://github.com/astroautomata/SymbolicRegression.jl/commit/788ce37f48c9106a95c2158be3aa137a0cea8bca))

### Bug Fixes

- distributed TensorBoardLogging ([272195e](https://github.com/astroautomata/SymbolicRegression.jl/commit/272195e8057693d4908800c66ed5c7f1d8c11548))

## [1.0.3](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.0.2...v1.0.3) (2024-11-28)

### Features

- allow argument-less TemplateExpression parts ([f4c0d7c](https://github.com/astroautomata/SymbolicRegression.jl/commit/f4c0d7c51b83fa52d39be23f5359db93c126bc44))
- allow argument-less TemplateExpression parts ([6d2a72d](https://github.com/astroautomata/SymbolicRegression.jl/commit/6d2a72d0d42d5aeda4c3f9b75231319cef420575))

### Bug Fixes

- `predict` for TemplateExpressions ([808bd10](https://github.com/astroautomata/SymbolicRegression.jl/commit/808bd10111a1232ec722f1f6a89ffb7a4417bb68))
- `predict` for TemplateExpressions ([3f4b201](https://github.com/astroautomata/SymbolicRegression.jl/commit/3f4b201254e5a80af67843d2e997aa6ec1227506))

## [1.0.2](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.0.1...v1.0.2) (2024-11-24)

### Bug Fixes

- widen type constraints for TemplateExpression ([b5fc8eb](https://github.com/astroautomata/SymbolicRegression.jl/commit/b5fc8eb63bbd48444266c6dcb862c88ead7717db))
- widen type constraints for TemplateExpression evaluation ([dedb41a](https://github.com/astroautomata/SymbolicRegression.jl/commit/dedb41a6b7c40f97e74d361046d34717d83f2fb9))

## [1.0.1](https://github.com/astroautomata/SymbolicRegression.jl/compare/v1.0.0...v1.0.1) (2024-11-20)

## SymbolicRegression.jl v1.0.0

New URL: https://ai.damtp.cam.ac.uk/symbolicregression

Summary of major recent changes, described in more detail below:

1. Changed the core expression type from `Node{T} → Expression{T,Node{T},Metadata{...}}`
   - This gives us new features, improves user hackability, and greatly improves ergonomics!
2. Created "_Template Expressions_", for fitting expressions under a user-specified functional form (`TemplateExpression <: AbstractExpression`)
   - Template expressions are quite flexible: they are a meta-expression that wraps multiple other expressions, and combines them using a user-specified function.
   - This enables **vector expressions** - in other words, you can learn multiple components of a vector, simultaneously, with a single expression! Or more generally, you can learn expressions onto any Julia struct.
     - (Note that this still does not permit learning using non-scalar operators, though we are working on that!)
   - Template expressions also make use of colored strings to represent each part in the printout, to improve readability.
3. Created "_Parametric Expressions_", for custom functional forms with per-class parameters: (`ParametricExpression <: AbstractExpression`)
   - This lets you fit expressions that act as _models of multiple systems_, with per-system parameters!
4. Introduced a variety of new abstractions for user extensibility (**and to support new research on symbolic regression!**)
   - `AbstractExpression`, for increased flexibility in custom expression types.
   - `mutate!` and `AbstractMutationWeights`, for user-defined mutation operators.
   - `AbstractSearchState`, for holding custom metadata during searches.
   - `AbstractOptions` and `AbstractRuntimeOptions`, for customizing pretty much everything else in the library via multiple dispatch. Please make an issue/PR if you would like any particular internal functions be declared `public` to enable stability across versions for your tool.
   - Many of these were motivated to modularize the implementation of [LaSR](https://github.com/trishullab/LibraryAugmentedSymbolicRegression.jl), an LLM-guided version of SymbolicRegression.jl, so it can sit as a modular layer on top of SymbolicRegression.jl.
5. Added TensorBoardLogger.jl and other logging integrations via `SRLogger`
6. Support for Zygote.jl and Enzyme.jl within the constant optimizer, specified using the `autodiff_backend` option
7. Other changes:
   - Fundamental improvements to the underlying evolutionary algorithm
     - New mutation operators introduced, `swap_operands` and `rotate_tree` – both of which seem to help kick the evolution out of local optima.
     - New hyperparameter defaults created, based on a Pareto front volume calculation, rather than simply accuracy of the best expression.
   - Changed output file handling
   - Major refactoring of the codebase to improve readability and modularity
   - Identified and fixed a major internal bug involving unexpected aliasing produced by the crossover operator
     - Segmentation faults caused by this are a likely culprit for some crashes reported during multi-day multi-node searches.
     - Introduced a new test for aliasing throughout the entire search state to prevent this from happening again.
   - Improved progress bar and StyledStrings integration.
   - Julia 1.10 is now the minimum supported Julia version.
   - Other small features
   - Also see the "Update Guide" below for more details on upgrading.

Note that some of these features were recently introduced in patch releases since they were backwards compatible. I am noting them here for visibility.

### 1. Changed the core expression type from `Node{T} → Expression{T,Node{T},...}`

<details>

https://github.com/MilesCranmer/SymbolicRegression.jl/pull/326

This is a breaking change in the format of expressions returned by SymbolicRegression. Now, instead of returning a `Node{T}`, SymbolicRegression will return a `Expression{T,Node{T},...}` (both from `equation_search` and from `report(mach).equations`). This type is much more convenient and high-level than the `Node` type, as it includes metadata relevant for the node, such as the operators and variable names.

This means you can reliably do things like:

```julia
using SymbolicRegression: Options, Expression, Node

options = Options(binary_operators=[+, -, *, /], unary_operators=[cos, exp, sin])
operators = options.operators
variable_names = ["x1", "x2", "x3"]
x1, x2, x3 = [Expression(Node(Float64; feature=i); operators, variable_names) for i=1:3]

## Use the operators directly!
tree = cos(x1 - 3.2 * x2) - x1 * x1
```

You can then do operations with this `tree`, without needing to track `operators`:

```julia
println(tree)  # Looks up the right operators based on internal metadata

X = randn(3, 100)

tree(X)  # Call directly!
tree'(X)  # gradients of expression
```

Each time you use an operator on or between two `Expression`s that include the operator in its list, it will look up the right enum index, and create the correct `Node`, and then return a new `Expression`.

You can access the tree with `get_tree` (guaranteed to return a `Node`), or `get_contents` – which returns the full info of an `AbstractExpression`, which might contain multiple expressions (which get stitched together when calling `get_tree`).

</details>

</details>

### 2. Created "_Template Expressions_", for fitting expressions under a user-specified functional form (`TemplateExpression <: AbstractExpression`)

<details>

Template Expressions allow users to define symbolic expressions with a fixed structure, combining multiple sub-expressions under user-specified constraints. This is particularly useful for symbolic regression tasks where domain-specific knowledge or constraints must be imposed on the model's structure.

This also lets you fit vector expressions using SymbolicRegression.jl, where vector components can also be shared!

A `TemplateExpression` is constructed by specifying:

- A named tuple of sub-expressions (e.g., `(; f=x1 - x2 * x2, g=1.5 * x3)`).
- A structure function that defines how these sub-expressions are combined in different contexts.

For example, you can create a `TemplateExpression` that enforces the constraint: `sin(f(x1, x2)) + g(x3)^2` - where we evolve `f` and `g` simultaneously.

To do this, we first describe the structure using `TemplateStructure` that takes a single closure function that maps a named tuple of `ComposableExpression` expressions and a tuple of features:

```julia
using SymbolicRegression

structure = TemplateStructure{(:f, :g)}(
  ((; f, g), (x1, x2, x3)) -> sin(f(x1, x2)) + g(x3)^2
)
```

This defines how the `TemplateExpression` should be evaluated numerically on a given input.

The number of arguments allowed by each expression object is inferred using this closure, though it can also be passed explicitly with the `num_features` kwarg.

```julia
operators = Options(binary_operators=(+, -, *, /)).operators
variable_names = ["x1", "x2", "x3"]
x1 = ComposableExpression(Node{Float64}(; feature=1); operators, variable_names)
x2 = ComposableExpression(Node{Float64}(; feature=2); operators, variable_names)
x3 = ComposableExpression(Node{Float64}(; feature=3); operators, variable_names)
```

Note that using `x1` here refers to the _relative_ argument to the expression. So the node with feature equal to 1 will reference the first argument, regardless of what it is.

```julia
st_expr = TemplateExpression(
    (; f=x1 - x2 * x2, g=1.5 * x1);
    structure,
    operators,
    variable_names
) # Prints as: f = #1 - (#2 * #2); g = 1.5 * #1

# Evaluation combines evaluation of `f` and `g`, and combines them
# with the structure function:
st_expr([0.0; 1.0; 2.0;;])
```

This also work with hierarchical expressions! For example,

```julia
structure = TemplateStructure{(:f, :g)}(
  ((; f, g), (x1, x2, x3)) -> f(x1, g(x2), x3^2) - g(x3)
)
```

this is a valid structure!

We can also use this `TemplateExpression` in SymbolicRegression.jl searches!

<details>
<summary>For example, say that we want to fit *vector expressions*:</summary>

```julia
using SymbolicRegression
using MLJBase: machine, fit!, report
```

We first define our structure. This also has our variable mapping, which says we are fitting `f(x1, x2)`, `g1(x3)`, and `g2(x3)`:

```julia
function my_structure((; f, g1, g2), (x1, x2, x3))
    _f = f(x1, x2)
    _g1 = g1(x3)
    _g2 = g2(x3)

    # We use `.x` to get the underlying vector
    out = map((fi, g1i, g2i) -> (fi + g1i, fi + g2i), _f.x, _g1.x, _g2.x)
    # And `.valid` to see whether the evaluations
    return ValidVector(out, _f.valid && _g1.valid && _g2.valid)
end
structure = TemplateStructure{(:f, :g1, :g2)}(my_structure)
```

Now, our dataset is a regular 2D array of inputs for `X`. But our `y` is actually a _vector of 2-tuples_!

```julia
X = rand(100, 3) .* 10

y = [
    (sin(X[i, 1]) + X[i, 3]^2, sin(X[i, 1]) + X[i, 3])
    for i in eachindex(axes(X, 1))
]
```

Now, since this is a vector-valued expression, we need to specify a custom `elementwise_loss` function:

```julia
elementwise_loss = ((x1, x2), (y1, y2)) -> (y1 - x1)^2 + (y2 - x2)^2
```

This reduces `y` and the predicted value of `y` returned by the structure function.

Our regressor is then:

```julia
model = SRRegressor(;
    binary_operators=(+, *),
    unary_operators=(sin,),
    maxsize=15,
    elementwise_loss=elementwise_loss,
    expression_type=TemplateExpression,
    # Note - this is where we pass custom options to the expression type:
    expression_options=(; structure),
)

mach = machine(model, X, y)
fit!(mach)
```

Let's see the performance of the model:

```julia
report(mach)
```

We can also check the expression is split up correctly:

```julia
r = report(mach)
idx = r.best_idx
best_expr = r.equations[idx]
best_f = get_contents(best_expr).f
best_g1 = get_contents(best_expr).g1
best_g2 = get_contents(best_expr).g2
```

</details>

</details>

### 3. Created "_Parametric Expressions_", for custom functional forms with per-class parameters: (`ParametricExpression <: AbstractExpression`)

<details>

Parametric Expressions are another example of an `AbstractExpression` with additional features than a normal `Expression`. This type allows SymbolicRegression.jl to fit a _parametric functional form_, rather than an expression with fixed constants. This is particularly useful when modeling multiple systems or categories where each may have unique parameters but share a common functional form and certain constants.

A parametric expression is constructed with a tree represented as a `ParametricNode <: AbstractExpressionNode` – this is an alternative type to the usual `Node` type which includes extra fields: `is_parameter::Bool`, and `parameter::UInt16`. A `ParametricExpression` wraps this type and stores the actual parameter matrix (under `.metadata.parameters`) as well as the parameter names (under `.metadata.parameter_names`).

Various internal functions have been overloaded for custom behavior when fitting parametric expressions. For example, `mutate_constant` will perturb a row of the parameter matrix, rather than a single parameter.

When fitting a `ParametricExpression`, the `expression_options` parameter in `Options/SRRegressor` should include a `max_parameters` keyword, which specifies the maximum number of separate parameters in the functional form.

<details>
<summary>Let's see an example of fitting a parametric expression:</summary>

```julia
using SymbolicRegression
using Random: MersenneTwister
using Zygote
using MLJBase: machine, fit!, predict, report
```

Let's generate two classes of model and try to find it:

```julia
rng = MersenneTwister(0)
X = NamedTuple{(:x1, :x2, :x3, :x4, :x5)}(ntuple(_ -> randn(rng, Float32, 30), Val(5)))
X = (; X..., classes=rand(rng, 1:2, 30))  # Add class labels (1 or 2)

# Define per-class parameters
p1 = [0.0f0, 3.2f0]
p2 = [1.5f0, 0.5f0]

# Generate target variable y with class-specific parameters
y = [
    2 * cos(X.x4[i] + p1[X.classes[i]]) + X.x1[i]^2 - p2[X.classes[i]]
    for i in eachindex(X.classes)
]
```

When fitting a `ParametricExpression`, it tends to be more important to set up an `autodiff_backend` such as `:Zygote` or `:Enzyme`, as the default backend (finite differences) can be too slow for the high-dimensional parameter spaces.

```julia
model = SRRegressor(
    niterations=100,
    binary_operators=[+, *, /, -],
    unary_operators=[cos, exp],
    populations=30,
    expression_type=ParametricExpression,
    expression_options=(; max_parameters=2),  # Allow up to 2 parameters
    autodiff_backend=:Zygote,  # Use Zygote for automatic differentiation
    parallelism=:multithreading,
)

mach = machine(model, X, y)

fit!(mach)
```

The expressions are returned with the parameters:

```julia
r = report(mach);
best_expr = r.equations[r.best_idx]
@show best_expr
@show get_metadata(best_expr).parameters
```

</details>

</details>

### 4. Introduced a variety of new abstractions for user extensibility

<details>

v1 introduces several new abstract types to improve extensibility. These allow you to define custom behaviors by leveraging Julia's multiple dispatch system.

**Expression types**: `AbstractExpression`: As explained above, SymbolicRegression now works on `Expression` rather than `Node`, by default. Actually, most internal functions in SymbolicRegression.jl are now defined on `AbstractExpression`, which allows overloading behavior. The expression type used can be modified with the `expression_type` and `node_type` options in `Options`.

- `expression_type`: By default, this is `Expression`, which simply stores a binary tree (`Node`) as well as the `variable_names::Vector{String}` and `operators::DynamicExpressions.OperatorEnum`. See the implementation of `TemplateExpression` and `ParametricExpression` for examples of what needs to be overloaded.
- `node_type`: By default, this will be `DynamicExpressions.default_node_type(expression_type)`, which allows `ParametricExpression` to default to `ParametricNode` as the underlying node type.

**Mutation types**: `mutate!(tree::N, member::P, ::Val{S}, mutation_weights::AbstractMutationWeights, options::AbstractOptions; kws...) where {N<:AbstractExpression,P<:PopMember,S}`, where `S` is a symbol representing the type of mutation to perform (where the symbols are taken from the `mutation_weights` fields). This allows you to define new mutation types by subtyping `AbstractMutationWeights` and creating new `mutate!` methods (simply pass the `mutation_weights` instance to `Options` or `SRRegressor`).

**Search states**: `AbstractSearchState`: this is the abstract type for `SearchState` which stores the search process's state (such as the populations and halls of fame). For advanced users, you may wish to overload this to store additional state details. (For example, [LaSR](https://github.com/trishullab/LibraryAugmentedSymbolicRegression.jl) stores some history of the search process to feed the language model.)

**Global options and full customization**: `AbstractOptions` and `AbstractRuntimeOptions`: Many functions throughout SymbolicRegression.jl take `AbstractOptions` as an input. The default assumed implementation is `Options`. However, you can subtype `AbstractOptions` to overload certain behavior.

For example, if we have new options that we want to add to `Options`:

```julia
Base.@kwdef struct MyNewOptions
    a::Float64 = 1.0
    b::Int = 3
end
```

we can create a combined options type that forwards properties to each corresponding type:

```julia
struct MyOptions{O<:SymbolicRegression.Options} <: SymbolicRegression.AbstractOptions
    new_options::MyNewOptions
    sr_options::O
end
const NEW_OPTIONS_KEYS = fieldnames(MyNewOptions)

# Constructor with both sets of parameters:
function MyOptions(; kws...)
    new_options_keys = filter(k -> k in NEW_OPTIONS_KEYS, keys(kws))
    new_options = MyNewOptions(; NamedTuple(new_options_keys .=> Tuple(kws[k] for k in new_options_keys))...)
    sr_options_keys = filter(k -> !(k in NEW_OPTIONS_KEYS), keys(kws))
    sr_options = SymbolicRegression.Options(; NamedTuple(sr_options_keys .=> Tuple(kws[k] for k in sr_options_keys))...)
    return MyOptions(new_options, sr_options)
end

# Make all `Options` available while also making `new_options` accessible
function Base.getproperty(options::MyOptions, k::Symbol)
    if k in NEW_OPTIONS_KEYS
        return getproperty(getfield(options, :new_options), k)
    else
        return getproperty(getfield(options, :sr_options), k)
    end
end

Base.propertynames(options::MyOptions) = (NEW_OPTIONS_KEYS..., fieldnames(SymbolicRegression.Options)...)
```

These new abstractions provide users with greater flexibility in defining the structure and behavior of expressions, nodes, and the search process itself. These are also of course used as the basis for alternate behavior such as `ParametricExpression` and `TemplateExpression`.

</details>

### 5. Added TensorBoardLogger.jl and other logging integrations via `SRLogger`

<details>

You can now track the progress of symbolic regression searches using `TensorBoardLogger.jl`, `Wandb.jl`, or other logging backends.

This is done by wrapping any `AbstractLogger` with the new `SRLogger` type, and passing it to the `logger` option in `SRRegressor` or `equation_search`:

```julia
using SymbolicRegression
using TensorBoardLogger

logger = SRLogger(
    TBLogger("logs/run"),
    log_interval=2,  # Log every 2 steps
)

model = SRRegressor(;
    binary_operators=[+, -, *],
    logger=logger,
)
```

The logger will track:

- Loss curves over time at each complexity level
- Population statistics (distribution of complexities)
- Pareto frontier volume (can be used as an overall metric of search performance)
- Full equations at each complexity level

This works with any logger that implements the Julia logging interface.

</details>

### 6. Support for Zygote.jl and Enzyme.jl within the constant optimizer, specified using the `autodiff_backend` option

<details>

Historically, SymbolicRegression has mostly relied on finite differences to estimate derivatives – which actually works well for small numbers of parameters. This is what Optim.jl selects unless you can provide it with gradients.

However, with the introduction of `ParametricExpression`s, full support for autodiff-within-Optim.jl was needed. v1 includes support for some parts of DifferentiationInterface.jl, allowing you to actually turn on various automatic differentiation backends when optimizing constants. For example, you can use

```julia
Options(
    autodiff_backend=:Zygote,
)
```

to use Zygote.jl for autodiff during BFGS optimization, or even

```julia
Options(
    autodiff_backend=:Enzyme,
)
```

for Enzyme.jl (though Enzyme support is highly experimental).

</details>

### 7. Other Changes

<details>

#### Changed output file handling

Instead of writing to a single file like `hall_of_fame_<timestamp>.csv`, outputs are now organized in a directory structure. Each run gets a unique ID (containing a timestamp and random string, e.g., `20240315_120000_x7k92p`), and outputs are saved to `outputs/<run_id>/`. Currently, only saves `hall_of_fame.csv` (and `hall_of_fame.csv.bak`), with plans to add more logs and diagnostics in this folder in future releases.

The output directory can be customized via the `output_directory` option (defaults to `./outputs`). A custom run ID can be specified via the new `run_id` parameter passed to `equation_search` (or `SRRegressor`).

#### Other Small Features in v1.0.0

- Support for per-variable complexity, via the `complexity_of_variables` option.
- Option to force dimensionless constants when fitting with dimensional constraints, via the `dimensionless_constants_only` option.
- Default `maxsize` increased from 20 to 30.
- Default `niterations` increased from 10 to 50, as many users seem to be unaware that this is small (and meant for testing), even in publications. I think this 50 is still low, but it should be a more accurate default for those who don't tune.
- `MLJ.fit!(mach)` now records the number of iterations used, and, should `mach.model.niterations` be changed after the fit, the number of iterations passed to `equation_search` will be reduced accordingly.
- Fundamental improvements to the underlying evolutionary algorithm
  - New mutation operators introduced, `swap_operands` and `rotate_tree` – both of which seem to help kick the evolution out of local optima.
  - New hyperparameter defaults created, based on a Pareto front volume calculation, rather than simply accuracy of the best expression.
- Major refactoring of the codebase to improve readability and modularity
- Identified and fixed a major internal bug involving unexpected aliasing produced by the crossover operator
  - Segmentation faults caused by this are a likely culprit for some crashes reported during multi-day multi-node searches.
  - Introduced a new test for aliasing throughout the entire search state to prevent this from happening again.
- Improved progress bar and StyledStrings integration.
- Julia 1.10 is now the minimum supported Julia version.
- Also see the "Update Guide" below for more details on upgrading.

#### Update Guide

Note that most code should work without changes! Only if you are interacting with the return types of `equation_search` or `report(mach)`, or if you have modified any internals, should you need to make some changes.

Also note that the "_hall of fame_" CSV file is now stored in a directory structure, of the form `outputs/<run_id>/hall_of_fame.csv`. This is to accommodate additional log files without polluting the current working directory. Multi-output runs are now stored in the format `.../hall_of_fame_output1.csv`, rather than the old format `hall_of_fame_{timestamp}.csv.out1`.

So, the key changes are, as discussed above, the change from `Node` to `Expression` as the default type for representing expressions. This includes the hall of fame object returned by `equation_search`, as well as the vector of expressions stored in `report(mach).equations` for the MLJ interface. If you need to interact with the internal tree structure, you can use `get_contents(expression)` (which returns the tree of an `Expression`, or the named tuple of a `ParametricExpression` - use `get_tree` to map it to a single tree format).

To access other info stored in expressions, such as the operators or variable names, use `get_metadata(expression)`.

This also means that expressions are now basically self-contained. Functions like `eval_tree_array` no longer require options as arguments (though you can pass it to override the expression's stored options). This means you can also simply call the expression directly with input data (in `[n_features, n_rows]` format).

Before this change, you might have written something like this:

```julia
using SymbolicRegression

x1 = Node{Float64}(; feature=1)
options = Options(; binary_operators=(+, *))
tree = x1 * x1
```

This had worked, but only because of some spooky action at a distance behavior involving a global store of last-used operators! (Noting that `Node` simply stores an index to the operator to be lightweight.)

After this change, things are much cleaner:

```julia
options = Options(; binary_operators=(+, *))
operators = options.operators
variable_names = ["x1"]
x1 = Expression(Node{Float64}(; feature=1); operators, variable_names)

tree = x1 * x1
```

This is now a safe and explicit construction, since `*` can lookup what operators each expression uses, and infer the right indices! This `operators::OperatorEnum` is a tuple of functions, so does not incur dispatch costs at runtime. (The `variable_names` is optional, and gets stripped during the evolution process, but is embedded when returned to the user.)

We can now use this directly:

```julia
println(tree)       # Uses the `variable_names`, if stored
tree(randn(1, 50))  # Evaluates the expression using the stored operators
```

Also note that the minimum supported version of Julia is now 1.10. This is because Julia 1.9 and earlier have now reached end-of-life status, and 1.10 is the new LTS release.

#### Additional Notes

- **Custom Loss Functions**: Continue to define these on `AbstractExpressionNode`.
- **General Usage**: Most existing code should work with minimal changes.
- **CI Updates**: Tests are now split into parts for faster runs, and use TestItems.jl for better scoping of test variables.

</details>

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.24.5...v1.0.0

## SymbolicRegression.jl v0.24.5

### SymbolicRegression v0.24.5

[Diff since v0.24.4](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.24.4...v0.24.5)

**Merged pull requests:**

- ci: split up test suite into multiple runners (#311) (@MilesCranmer)
- chore(deps): bump julia-actions/cache from 1 to 2 (#315) (@dependabot[bot])
- CompatHelper: bump compat for DynamicQuantities to 0.14, (keep existing compat) (#317) (@github-actions[bot])
- Use DispatchDoctor.jl to wrap entire package with `@stable` (#321) (@MilesCranmer)
- CompatHelper: bump compat for MLJModelInterface to 1, (keep existing compat) (#322) (@github-actions[bot])
- Mark more functions as stable (#323) (@MilesCranmer)
- Allow per-variable complexity (#324) (@MilesCranmer)
- Refactor tests to use TestItems.jl (#325) (@MilesCranmer)

## SymbolicRegression.jl v0.24.4

### SymbolicRegression v0.24.4

[Diff since v0.24.3](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.24.3...v0.24.4)

**Merged pull requests:**

- feat: use `?` for wildcard units instead of `⋅` (#307) (@MilesCranmer)
- refactor: fix some more type instabilities (#308) (@MilesCranmer)
- refactor: remove unused Tricks dependency (#309) (@MilesCranmer)
- Add option to force dimensionless constants (#310) (@MilesCranmer)

## SymbolicRegression.jl v0.24.3

### SymbolicRegression v0.24.3

[Diff since v0.24.2](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.24.2...v0.24.3)

**Merged pull requests:**

- 40% speedup (for default settings) via more parallelism inside workers (#304) (@MilesCranmer)

**Closed issues:**

- Silence warnings for Optim.jl (#255)

## SymbolicRegression.jl v0.24.2

### SymbolicRegression v0.24.2

[Diff since v0.24.1](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.24.1...v0.24.2)

**Merged pull requests:**

- Bump julia-actions/setup-julia from 1 to 2 (#300) (@dependabot[bot])
- [pre-commit.ci] pre-commit autoupdate (#301) (@pre-commit-ci[bot])
- A small update on examples.md for 1-based indexing (#302) (@liuyxpp)
- Fixes for Julia 1.11 (#303) (@MilesCranmer)

**Closed issues:**

- API Overhaul (#187)
- [Feature]: Training on high dimensions X (#299)

## SymbolicRegression.jl v0.24.1

### What's Changed

- CompatHelper: bump compat for MLJModelInterface to 1.9, (keep existing compat) by @github-actions in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/295
- CompatHelper: bump compat for ProgressBars to 1, (keep existing compat) by @github-actions in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/294
- Ensure we load ClusterManagers.jl on workers by @MilesCranmer in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/297
- Move test dependencies to test folder by @MilesCranmer in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/298

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.24.0...v0.24.1

## SymbolicRegression.jl v0.24.0

### What's Changed

- Experimental support for program synthesis / graph-like expressions instead of trees (https://github.com/MilesCranmer/SymbolicRegression.jl/pull/271)
  - **BREAKING**: many types now have a third type parameter, declaring the type of node. For example, `PopMember{T,L}` is now `PopMember{T,L,N}` for `N` the type of expression.
  - Can now specify a `node_type` in creation of `Options`. This `node_type <: AbstractExpressionNode` can be a `GraphNode` which will result in expressions that care share nodes – and therefore have a lower complexity.
  - Two new mutations: `form_connection` and `break_connection` – which control the merging and breaking of shared nodes in expressions. These are experimental.
- **BREAKING**: The `Dataset` struct has had many of its field declared immutable (for memory safety). If you had relied on the mutability of the struct to set parameters after initializing it, you will need to modify your code.
- **BREAKING**: LoopVectorization.jl moved to a package extension. Need to install it separately (https://github.com/MilesCranmer/SymbolicRegression.jl/pull/287).
- **DEPRECATED**: Now prefer to use new keyword-based constructors for nodes:

```julia
Node{T}(feature=...)        # leaf referencing a particular feature column
Node{T}(val=...)            # constant value leaf
Node{T}(op=1, l=x1)         # operator unary node, using the 1st unary operator
Node{T}(op=1, l=x1, r=1.5)  # binary unary node, using the 1st binary operator
```

rather than the previous constructors `Node(op, l, r)` and `Node(T; val=...)` (though those will still work; just with a `depwarn`).

- Bumper.jl support added. Passing `bumper=true` to `Options()` will result in using bump-allocation for evaluation which can get speeds equivalent to LoopVectorization and sometimes even better due to better management of allocations. (https://github.com/MilesCranmer/SymbolicRegression.jl/pull/287)
- Upgraded Optim.jl to 1.9.
- Upgraded DynamicQuantities to 0.13
- Upgraded DynamicExpressions to 0.16
- The main search loop has been greatly refactored for readability and improved type inference. It now looks like this (down from a monolithic ~1000 line function)

```julia
function _equation_search(
    datasets::Vector{D}, ropt::RuntimeOptions, options::Options, saved_state
) where {D<:Dataset}
    _validate_options(datasets, ropt, options)
    state = _create_workers(datasets, ropt, options)
    _initialize_search!(state, datasets, ropt, options, saved_state)
    _warmup_search!(state, datasets, ropt, options)
    _main_search_loop!(state, datasets, ropt, options)
    _tear_down!(state, ropt, options)
    return _format_output(state, ropt)
end
```

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.23.3...v0.24.0

## SymbolicRegression.jl v0.23.3

### SymbolicRegression v0.23.3

[Diff since v0.23.2](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.23.2...v0.23.3)

**Merged pull requests:**

- Bump peter-evans/create-or-update-comment from 3 to 4 (#283) (@dependabot[bot])
- Bump peter-evans/find-comment from 2 to 3 (#284) (@dependabot[bot])
- Bump peter-evans/create-pull-request from 5 to 6 (#286) (@dependabot[bot])

## SymbolicRegression.jl v0.23.2

### SymbolicRegression v0.23.2

[Diff since v0.23.1](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.23.1...v0.23.2)

**Merged pull requests:**

- Formatting overhaul (#278) (@MilesCranmer)
- Avoid julia-formatter on pre-commit.ci (#279) (@MilesCranmer)
- Make it easier to select expression from Pareto front for evaluation (#289) (@MilesCranmer)

**Closed issues:**

- Garbage collection too passive on worker processes (#237)
- How can I set the maximum number of nests? (#285)

## SymbolicRegression.jl v0.23.1

### What's Changed

- Implement swap operands mutation for binary operators by @foxtran in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/276

### New Contributors

- @foxtran made their first contribution in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/276

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.23.0...v0.23.1

## SymbolicRegression.jl v0.23.0

### SymbolicRegression v0.23.0

[Diff since v0.22.5](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.22.5...v0.23.0)

**Merged pull requests:**

- Automatically set heap size hint on workers (#270) (@MilesCranmer)

**Closed issues:**

- How do I set up a basis function consisting of three different inputs x, y, z? (#268)

## SymbolicRegression.jl v0.22.5

### SymbolicRegression v0.22.5

[Diff since v0.22.4](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.22.4...v0.22.5)

**Merged pull requests:**

- CompatHelper: bump compat for DynamicQuantities to 0.7, (keep existing compat) (#259) (@github-actions[bot])
- Create `cond` operator (#260) (@MilesCranmer)
- Add `[compat]` entry for Documenter (#261) (@MilesCranmer)
- CompatHelper: bump compat for DynamicQuantities to 0.10 (#264) (@github-actions[bot])

## SymbolicRegression.jl v0.22.4

### SymbolicRegression v0.22.4

[Diff since v0.22.3](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.22.3...v0.22.4)

**Merged pull requests:**

- Hotfix for breaking change in Optim.jl (#256) (@MilesCranmer)
- Fix worldage issues by avoiding `static_hasmethod` when not needed (#258) (@MilesCranmer)

## SymbolicRegression.jl v0.22.3

### What's Changed

- CompatHelper: bump compat for DynamicExpressions to 0.13, (keep existing compat) by @github-actions in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/250
- Fix type stability of deterministic mode by @MilesCranmer in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/251
- Faster random sampling of nodes by @MilesCranmer in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/252
- Faster copying of `MutationWeights` by @MilesCranmer in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/253
- Hotfix for breaking change in Optim.jl by @MilesCranmer in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/256

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.22.2...v0.22.3

## SymbolicRegression.jl v0.22.2

### SymbolicRegression v0.22.2

[Diff since v0.22.1](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.22.1...v0.22.2)

**Merged pull requests:**

- Expand aqua test suite (#246) (@MilesCranmer)
- Return more descriptive errors for poorly defined operators (#247) (@MilesCranmer)

## SymbolicRegression.jl v0.22.1

### SymbolicRegression v0.22.1

[Diff since v0.22.0](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.22.0...v0.22.1)

## SymbolicRegression.jl v0.22.0

### What's Changed

- (**Algorithm modification**) Evaluate on fixed batch when building per-population hall of fame in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/243
  - This only affects searches that use `batching=true`. It results in improved searches on large datasets, as the "winning expression" is not biased towards an expression that landed on a lucky batch.
  - Note that this only occurs within an iteration. Evaluation on the entire dataset still happens at the end of an iteration and those loss measurements are used for absolute comparison between expressions.
- (**Algorithm modification**) Deprecates the `fast_cycle` feature in #243. Use of this parameter will have no effect.
  - Was removed to ease maintenance burden and because it doesn't have a use. This feature was created early on in development as a way to get parallelism within a population. It is no longer useful as you can parallelize across populations.
- Add Aqua.jl to test suite in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/245
- CompatHelper: bump compat for DynamicExpressions to 0.12, (keep existing compat) in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/242
  - Is able to avoids method invalidations when using operators to construct expressions manually by modifying a global constant mapping of operator => index, rather than `@eval`-ing new operators.
  - This only matters if you were using operators to build trees, like `x1 + x2`. All internal search code uses `Node()` explicitly to build expressions, so did not rely on method invalidation at any point.
- Renames some parameters in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/234
  - `npop` => `population_size`
  - `npopulations` => `populations`
  - This is just to match PySR's API. Also note that the deprecated parameters will still work, and there will not be a warning unless you are running with `--depwarn=yes`.
- Ensure that `predict` uses units if trained with them in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/244
  - If you train on a dataset that has physical units, this ensures that `MLJ.predict` will output predictions in the same units. Before this change, `MLJ.predict` would return numerical arrays with no units.

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.21.5...v0.22.0

## SymbolicRegression.jl v0.21.5

### What's Changed

- Allow custom display variable names by @MilesCranmer in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/240

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.21.4...v0.21.5

## SymbolicRegression.jl v0.21.4

### SymbolicRegression v0.21.4

[Diff since v0.21.3](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.21.3...v0.21.4)

**Closed issues:**

- [Cleanup] Better implementation of batching (#88)

**Merged pull requests:**

- CompatHelper: bump compat for LossFunctions to 0.11, (keep existing compat) (#238) (@github-actions[bot])
- Enable compatibility with MLJTuning.jl (#239) (@MilesCranmer)

## SymbolicRegression.jl v0.21.3

### What's Changed

- Batching inside optimization loop + batching support for custom objectives by @MilesCranmer in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/235

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.21.2...v0.21.3

## SymbolicRegression.jl v0.21.2

### What's Changed

- Allow empty string units (==1) by @MilesCranmer in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/233

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.21.1...v0.21.2

## SymbolicRegression.jl v0.21.1

### What's Changed

- Update DynamicExpressions.jl version by @MilesCranmer in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/232
  - Makes Zygote.jl an extension

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.21.0...v0.21.1

## SymbolicRegression.jl v0.21.0

### What's Changed

- https://github.com/MilesCranmer/SymbolicRegression.jl/pull/228 and https://github.com/MilesCranmer/SymbolicRegression.jl/pull/230 and https://github.com/MilesCranmer/SymbolicRegression.jl/pull/231
  - **Dimensional analysis** (#228)
    - Allows you to (softly) constrain discovered expressions to those that respect physical dimensions
    - Pass vectors of DynamicQuantities.jl `Quantity` type to the MLJ interface.
    - OR, specify `X_units`, `y_units` to low-level `equation_search`.
  - **Printing improvements** (#228)
    - By default, only 5 significant digits are now printed, rather than the entire float. You can change this with the `print_precision` option.
    - In the default printed equations, `x₁` is used rather than `x1`.
    - `y =` is printed at the start (or `y₁ =` for multi-output). With units this becomes, for example, `y[kg] =`.
  - **Misc**
    - Easier to convert from MLJ interface to SymbolicUtils (via `node_to_symbolic(::Node, ::AbstractSRRegressor)`) (#228)
    - Improved precompilation (#228)
    - Various performance and type stability improvements (#228)
    - Inlined the recording option to speedup compilation (#230)
    - Updated tutorials to use MLJ rather than low-level interface (#228)
    - Moved JSON3.jl to extension (#231)
    - Use PackageExtensionsCompat.jl over Requires.jl (#231)
    - Require LossFunctions.jl to be 0.10 (#231)

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.20.0...v0.21.0

## SymbolicRegression.jl v0.20.0

### SymbolicRegression v0.20.0

[Diff since v0.19.1](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.19.1...v0.20.0)

**Closed issues:**

- [Feature]: MLJ integration (#225)

**Merged pull requests:**

- MLJ Integration (#226) (@MilesCranmer, @OkonSamuel)

## SymbolicRegression.jl v0.19.1

### SymbolicRegression v0.19.1

[Diff since v0.19.0](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.19.0...v0.19.1)

**Merged pull requests:**

- CompatHelper: bump compat for StatsBase to 0.34, (keep existing compat) (#202) (@github-actions[bot])
- (Soft deprecation) change `varMap` to `variable_names` (#219) (@MilesCranmer)
- (Soft deprecation) rename `EquationSearch` to `equation_search` (#222) (@MilesCranmer)
- Fix equation splitting for unicode variables (#223) (@MilesCranmer)

## SymbolicRegression.jl v0.19.0

### What's Changed

- Time to load improved by 40% with the following changes in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/215
  - Moved SymbolicUtils.jl to extension/Requires.jl
  - Removed StaticArrays.jl as a dependency and implement tiny version of MVector
  - Removed `@generated` functions

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.18.0...v0.19.0

## SymbolicRegression.jl v0.18.0

### SymbolicRegression v0.18.0

[Diff since v0.17.1](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.17.1...v0.18.0)

**Merged pull requests:**

- Overload ^ if user passes explicitly (#201) (@MilesCranmer)
- Upgrade DynamicExpressions to 0.8; LossFunctions to 0.10 (#206) (@github-actions[bot])
- Show expressions evaluated per second (#209) (@MilesCranmer)
- Cache complexity of expressions whenever possible (#210) (@MilesCranmer)

## SymbolicRegression.jl v0.17.1

### SymbolicRegression v0.17.1

[Diff since v0.17.0](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.17.0...v0.17.1)

**Merged pull requests:**

- Faster custom losses (#197) (@MilesCranmer)
- Migrate from SnoopPrecompile to PrecompileTools (#198) (@timholy)

## SymbolicRegression.jl v0.17.0

### SymbolicRegression v0.17.0

[Diff since v0.16.3](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.16.3...v0.17.0)

**Closed issues:**

- troubles in pysr.install() (#196)

**Merged pull requests:**

- Multiple refactors: arbitrary data in `Dataset`, separate mutation weight conditioning, fix data races, cleaner API (#190) (@MilesCranmer)
- CompatHelper: bump compat for DynamicExpressions to 0.6, (keep existing compat) (#194) (@github-actions[bot])

## SymbolicRegression.jl v0.16.3

### SymbolicRegression v0.16.3

[Diff since v0.16.2](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.16.2...v0.16.3)

**Merged pull requests:**

- CompatHelper: bump compat for SymbolicUtils to 1, (keep existing compat) (#168) (@github-actions[bot])

## SymbolicRegression.jl v0.16.2

### What's Changed

- Turn off simplification when constraints given by @MilesCranmer in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/189

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.16.1...v0.16.2

## SymbolicRegression.jl v0.16.1

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.16.0...v0.16.1

## SymbolicRegression.jl v0.16.0

### SymbolicRegression v0.16.0

[Diff since v0.15.3](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.15.3...v0.16.0)

**Closed issues:**

- Partially fixed trees (#166)
- Settings of `addprocs` (#180)
- Equation printout should split into multiple lines (#182)

**Merged pull requests:**

- Force safe closing of threads (#175) (@MilesCranmer)
- Abstract number support (#183) (@MilesCranmer)
- Include datetime in default filename (#185) (@MilesCranmer)

## SymbolicRegression.jl v0.15.3

### What's Changed

- Re-compute losses for warm start by @MilesCranmer in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/177

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.15.2...v0.15.3

## SymbolicRegression.jl v0.15.2

### What's Changed

- Include depth check in `check_constraints` by @MilesCranmer in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/172
- Fix data race in state saving by @MilesCranmer in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/173

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.15.1...v0.15.2

## SymbolicRegression.jl v0.15.1

### What's Changed

- Fix bug in constraint checking by @MilesCranmer in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/171

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.15.0...v0.15.1

## SymbolicRegression.jl v0.15.0

### What's Changed

- Fully-customizable training objectives by @MilesCranmer in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/143
- Safely catch non-readable stdin stream by @MilesCranmer in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/169

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.14.5...v0.15.0

## SymbolicRegression.jl v0.14.5

### SymbolicRegression v0.14.5

[Diff since v0.14.4](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.14.4...v0.14.5)

**Closed issues:**

- Large test output (#159)

**Merged pull requests:**

- Quiet progress bar during CI (#160) (@MilesCranmer)
- Proper SnoopCompilation (#161) (@MilesCranmer)

## SymbolicRegression.jl v0.14.4

### SymbolicRegression v0.14.4

[Diff since v0.14.3](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.14.3...v0.14.4)

**Merged pull requests:**

- Refactor monitoring of resources (#158) (@MilesCranmer)

## SymbolicRegression.jl v0.14.3

### SymbolicRegression v0.14.3

[Diff since v0.14.2](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.14.2...v0.14.3)

**Merged pull requests:**

- Turn off safe operators for turbo=true (#156) (@MilesCranmer)
- Use `ProgressBars.jl` instead of copying (#157) (@MilesCranmer)

## SymbolicRegression.jl v0.14.2

### SymbolicRegression v0.14.2

[Diff since v0.14.1](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.14.1...v0.14.2)

## SymbolicRegression.jl v0.14.1

### SymbolicRegression v0.14.1

[Diff since v0.14.0](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.14.0...v0.14.1)

**Merged pull requests:**

- Do optimizations as a low-probability mutation (#154) (@MilesCranmer)

## SymbolicRegression.jl v0.14.0

### SymbolicRegression v0.14.0

[Diff since v0.13.3](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.13.3...v0.14.0)

**Merged pull requests:**

- Add `@extend_operators` from DynamicExpressions.jl v0.4.0 (#153) (@MilesCranmer)

## SymbolicRegression.jl v0.13.3

### SymbolicRegression v0.13.3

[Diff since v0.13.1](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.13.1...v0.13.3)

**Merged pull requests:**

- 30% speed up by using LoopVectorization in DynamicExpressions.jl (#151) (@MilesCranmer)

## SymbolicRegression.jl v0.13.2

- Allow strings to be passed for the `parallelism` argument of EquationSearch (e.g., `"multithreading"` instead of `:multithreading`). This is to allow compatibility with PyJulia calls, which can't pass symbols.

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.13.1...v0.13.2

## SymbolicRegression.jl v0.13.1

### SymbolicRegression v0.13.1

[Diff since v0.13.0](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.13.0...v0.13.1)

**Merged pull requests:**

- Refactor mutation probabilities (#140) (@MilesCranmer)

## SymbolicRegression.jl v0.13.0

### SymbolicRegression v0.13.0

[Diff since v0.12.6](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.12.6...v0.13.0)

**Merged pull requests:**

- Split codebase in two: DynamicExpressions.jl and SymbolicRegression.jl (#147) (@MilesCranmer)

## SymbolicRegression.jl v0.12.6

### SymbolicRegression v0.12.6

[Diff since v0.12.5](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.12.5...v0.12.6)

**Closed issues:**

- [Feature] Integration of Existing Knowledge (#139)
- Search fidelity is much worse after v0.12.3 (#148)

**Merged pull requests:**

- Fix search performance problem #148 (#149) (@MilesCranmer)

## SymbolicRegression.jl v0.12.5

### SymbolicRegression v0.12.5

[Diff since v0.12.4](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.12.4...v0.12.5)

## SymbolicRegression.jl v0.12.4

### SymbolicRegression v0.12.4

[Diff since v0.12.3](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.12.3...v0.12.4)

**Merged pull requests:**

- Create logo (#145) (@MilesCranmer)

## SymbolicRegression.jl v0.12.3

### SymbolicRegression v0.12.3

[Diff since v0.12.2](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.12.2...v0.12.3)

**Merged pull requests:**

- Even faster evaluation (#144) (@MilesCranmer)

## SymbolicRegression.jl v0.12.2

### SymbolicRegression v0.12.2

[Diff since v0.12.1](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.12.1...v0.12.2)

**Closed issues:**

- How to fix a number of variables in predicted equations (#130)

**Merged pull requests:**

- Fast evaluation for constant trees (#129) (@MilesCranmer)

## SymbolicRegression.jl v0.12.1

### SymbolicRegression v0.12.1

[Diff since v0.12.0](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.12.0...v0.12.1)

## SymbolicRegression.jl v0.12.0

### What's Changed

- Use functions returning NaN on branch cuts instead of abs (issue #109) by @johanbluecreek in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/123
  - By returning NaN, an expression will have infinite loss - this will make the expression search simply avoid expressions that hit out-of-domain errors, rather than using `abs` everywhere which results in fundamentally different functional forms.
- Generalize `Node{T}` type to non-floats by @MilesCranmer in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/122
  - Will eventually enable integer-only expression searches

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.11.1...v0.12.0

## SymbolicRegression.jl v0.11.1

### What's Changed

- Generalize expressions to have arbitrary constant types by @MilesCranmer in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/119
- Optimizer options by @johanbluecreek in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/121
- Fix recorder when `Inf` appears as loss for expression
- Fix normalization when dataset has zero variance: https://github.com/MilesCranmer/SymbolicRegression.jl/commit/85f4909e8156ba8ff6cf89122371901a13df5688
- Set default parsimony to 0.0

### New Contributors

- @johanbluecreek made their first contribution in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/121

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.10.2...v0.11.1

## SymbolicRegression.jl v0.10.2

### SymbolicRegression v0.10.2

[Diff since v0.9.7](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.9.7...v0.10.2)

**Merged pull requests:**

- Update losses.md (#114) (@pitmonticone)
- Set `timeout-minutes` for CI (#116) (@rikhuijzer)

## SymbolicRegression.jl v0.9.7

### SymbolicRegression v0.9.7

[Diff since v0.9.6](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.9.6...v0.9.7)

## SymbolicRegression.jl v0.9.6

### SymbolicRegression v0.9.6

[Diff since v0.9.5](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.9.5...v0.9.6)

## SymbolicRegression.jl v0.9.5

### What's Changed

- Add deterministic option in https://github.com/MilesCranmer/SymbolicRegression.jl/pull/108
- Fix issue with infinite while loop due to numerical precision

**Full Changelog**: https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.9.3...v0.9.5

## SymbolicRegression.jl v0.9.3

### SymbolicRegression v0.9.3

[Diff since v0.9.2](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.9.2...v0.9.3)

**Merged pull requests:**

- CompatHelper: bump compat for LossFunctions to 0.8, (keep existing compat) (#106) (@github-actions[bot])

## SymbolicRegression.jl v0.9.2

### SymbolicRegression v0.9.2

[Diff since v0.9.0](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.9.0...v0.9.2)

**Closed issues:**

- Q : recording # of function calls (#74)
- Mangled name from @FromFile displayed in docs (#78)
- Consistent snake_case vs CamelCase (#85)

**Merged pull requests:**

- Apply Blue formatting + change all internal methods to snake_case (#100) (@MilesCranmer)
- Limiting max evaluations (#104) (@MilesCranmer)
- Custom complexities of operators, variables, and constants (#105) (@MilesCranmer)

## SymbolicRegression.jl v0.9.0

### SymbolicRegression v0.9.0

[Diff since v0.8.7](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.8.7...v0.9.0)

**Closed issues:**

- Update SymbolicUtils (#98)

**Merged pull requests:**

- Bump SymbolicUtils.jl to 0.19 (#84) (@ChrisRackauckas)

## SymbolicRegression.jl v0.8.7

### SymbolicRegression v0.8.7

[Diff since v0.8.6](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.8.6...v0.8.7)

## SymbolicRegression.jl v0.8.6

### SymbolicRegression v0.8.6

[Diff since v0.8.5](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.8.5...v0.8.6)

**Merged pull requests:**

- Switch from FromFile.jl to traditional module system (#95) (@MilesCranmer)
- Add constraints on the number of times operators can be nested (#96) (@MilesCranmer)

## SymbolicRegression.jl v0.8.5

### SymbolicRegression v0.8.5

[Diff since v0.8.3](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.8.3...v0.8.5)

**Closed issues:**

- [CLEANUP] Default settings (#72)
- forcing variables to regression (#87)

**Merged pull requests:**

- Autodiff for equations (#39) (@kazewong)
- fix worker connection timeout error (#91) (@CharFox1)
- Automatic multi-node compute setup by passing custom `addprocs` (#94) (@MilesCranmer)

## SymbolicRegression.jl v0.8.3

### SymbolicRegression v0.8.3

[Diff since v0.8.2](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.8.2...v0.8.3)

## SymbolicRegression.jl v0.8.2

### SymbolicRegression v0.8.2

[Diff since v0.8.1](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.8.1...v0.8.2)

**Closed issues:**

- Interactive regression / printing epochs (#80)

## SymbolicRegression.jl v0.8.1

### SymbolicRegression v0.8.1

[Diff since v0.7.13](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.7.13...v0.8.1)

**Closed issues:**

- [BUG] Domain errors (#71)
- [Performance] Single evaluation results (#73)

**Merged pull requests:**

- Refactoring PopMember + adding adaptive parsimony to tournament (#75) (@MilesCranmer)
- Introduce better default hyperparameters (#76) (@MilesCranmer)

## SymbolicRegression.jl v0.7.13

### SymbolicRegression v0.7.13

[Diff since v0.7.10](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.7.10...v0.7.13)

## SymbolicRegression.jl v0.7.10

### SymbolicRegression v0.7.10

[Diff since v0.7.9](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.7.9...v0.7.10)

## SymbolicRegression.jl v0.7.9

### SymbolicRegression v0.7.9

[Diff since v0.7.8](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.7.8...v0.7.9)

## SymbolicRegression.jl v0.7.8

### SymbolicRegression v0.7.8

[Diff since v0.7.7](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.7.7...v0.7.8)

**Closed issues:**

- Tournament selection p (#68)

**Merged pull requests:**

- Fix tournament samples (#70) (@MilesCranmer)

## SymbolicRegression.jl v0.7.7

### SymbolicRegression v0.7.7

[Diff since v0.7.6](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.7.6...v0.7.7)

## SymbolicRegression.jl v0.7.6

### SymbolicRegression v0.7.6

[Diff since v0.7.5](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.7.5...v0.7.6)

**Closed issues:**

- Parsimony interference in pareto frontier (#66)
- DomainError when computing pareto curve (#67)

## SymbolicRegression.jl v0.7.5

### SymbolicRegression v0.7.5

[Diff since v0.7.4](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.7.4...v0.7.5)

## SymbolicRegression.jl v0.7.4

### SymbolicRegression v0.7.4

[Diff since v0.7.3](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.7.3...v0.7.4)

**Closed issues:**

- Base.print (#64)

## SymbolicRegression.jl v0.7.3

### SymbolicRegression v0.7.3

[Diff since v0.7.2](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.7.2...v0.7.3)

## SymbolicRegression.jl v0.7.2

### SymbolicRegression v0.7.2

[Diff since v0.7.1](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.7.1...v0.7.2)

## SymbolicRegression.jl v0.7.1

### SymbolicRegression v0.7.1

[Diff since v0.7.0](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.7.0...v0.7.1)

**Merged pull requests:**

- CompatHelper: bump compat for SpecialFunctions to 2, (keep existing compat) (#56) (@github-actions[bot])

## SymbolicRegression.jl v0.7.0

### SymbolicRegression v0.7.0

[Diff since v0.6.19](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.6.19...v0.7.0)

**Closed issues:**

- Switching from Float to UInt8 ? (#58)

**Merged pull requests:**

- Revert to SymbolicUtils.jl 0.6 (#60) (@MilesCranmer)

## SymbolicRegression.jl v0.6.19

### SymbolicRegression v0.6.19

[Diff since v0.6.18](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.6.18...v0.6.19)

## SymbolicRegression.jl v0.6.18

### SymbolicRegression v0.6.18

[Diff since v0.6.17](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.6.17...v0.6.18)

## SymbolicRegression.jl v0.6.17

### SymbolicRegression v0.6.17

[Diff since v0.6.16](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.6.16...v0.6.17)

**Closed issues:**

- Can't define options as listed in Tutorial, causes Method Error. (#54)
- Using recorder to only track specific information? (#55)

## SymbolicRegression.jl v0.6.16

### SymbolicRegression v0.6.16

[Diff since v0.6.15](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.6.15...v0.6.16)

**Merged pull requests:**

- Expand compatibility to other SymbolicUtils.jl versions (#53) (@MilesCranmer)

## SymbolicRegression.jl v0.6.15

### SymbolicRegression v0.6.15

[Diff since v0.6.14](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.6.14...v0.6.15)

**Closed issues:**

- Unsatisfiable requirements detected for package SymbolicUtils (#51)

**Merged pull requests:**

- SymbolicUtils v0.18 (#50) (@AlCap23)

## SymbolicRegression.jl v0.6.14

### SymbolicRegression v0.6.14

[Diff since v0.6.13](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.6.13...v0.6.14)

**Closed issues:**

- nested task error (#43)
- MethodError: Cannot `convert` an object of type SymbolicUtils.Term{Number, Nothing} to an object of type SymbolicUtils.Pow{Number, SymbolicUtils.Term{Number, Nothing}, Float32, Nothing} (#44)

## SymbolicRegression.jl v0.6.13

### SymbolicRegression v0.6.13

[Diff since v0.6.12](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.6.12...v0.6.13)

## SymbolicRegression.jl v0.6.12

### SymbolicRegression v0.6.12

[Diff since v0.6.11](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.6.11...v0.6.12)

**Closed issues:**

- Options.npopulations = nothing, does not detect number of cores (#38)

**Merged pull requests:**

- Fix index functions in SymbolicUtils (#40) (@MilesCranmer)

## SymbolicRegression.jl v0.6.11

### SymbolicRegression v0.6.11

[Diff since v0.6.10](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.6.10...v0.6.11)

**Merged pull requests:**

- Updates for SymbolicUtils 0.13 (#37) (@AlCap23)

## SymbolicRegression.jl v0.6.10

### SymbolicRegression v0.6.10

[Diff since v0.6.9](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.6.9...v0.6.10)

**Closed issues:**

- Saving equations throughout runtime (#33)

**Merged pull requests:**

- Add multithreading as alternative to distributed (#34) (@MilesCranmer)
- Allow infinities in recorder (#36) (@cobac)

## SymbolicRegression.jl v0.6.9

### SymbolicRegression v0.6.9

[Diff since v0.6.8](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.6.8...v0.6.9)

## SymbolicRegression.jl v0.6.8

### SymbolicRegression v0.6.8

[Diff since v0.6.7](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.6.7...v0.6.8)

## SymbolicRegression.jl v0.6.7

### SymbolicRegression v0.6.7

[Diff since v0.6.6](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.6.6...v0.6.7)

## SymbolicRegression.jl v0.6.6

### SymbolicRegression v0.6.6

[Diff since v0.6.5](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.6.5...v0.6.6)

## SymbolicRegression.jl v0.6.5

### SymbolicRegression v0.6.5

[Diff since v0.6.4](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.6.4...v0.6.5)

## SymbolicRegression.jl v0.6.4

### SymbolicRegression v0.6.4

[Diff since v0.6.3](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.6.3...v0.6.4)

## SymbolicRegression.jl v0.6.3

### SymbolicRegression v0.6.3

[Diff since v0.6.2](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.6.2...v0.6.3)

## SymbolicRegression.jl v0.6.2

### SymbolicRegression v0.6.2

[Diff since v0.6.1](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.6.1...v0.6.2)

**Closed issues:**

- Data recorder (#27)
- Long-running parallel jobs have small percentage of processes hang (#28)

## SymbolicRegression.jl v0.6.1

### SymbolicRegression v0.6.1

[Diff since v0.6.0](https://github.com/MilesCranmer/SymbolicRegression.jl/compare/v0.6.0...v0.6.1)

**Merged pull requests:**

- Recorder and improved tournament selection (#29) (@MilesCranmer)
