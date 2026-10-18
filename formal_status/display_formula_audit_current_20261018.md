# Current-source mathematical review binding for all displayed formulas

Date: 2026-10-18. Current official source: `submission/current/manuscript.tex`.

- Current source SHA-256: `617cce1f87272bd5d5d58e3d91342bba658bb490cb901643fb9436ecc6e2894b`.
- Current source lines: 1910.
- Inventory: 240 display blocks, each bound below by source line, labels and exact display-block SHA-256.
- Prior review source: `submission/current/manuscript.tex` at commit `8b75977b138205c4ba402000b25d226d55994682`, SHA-256 `b1bb1e3df8d8b651c4872692a8b0f4424541b4e9b3a5576d39a2be485d26e23f`.
- Transfer rule: 235 display blocks are byte-identical to a block in the prior reviewed source; the row records its old display ID, line, and block hash. Five current-source changes/additions received the explicit delta review below.
- This is a source-binding and mathematical scope review record. Hash identity does not itself prove a Lean type semantically equivalent to a TeX statement; theorem correspondence remains in `submission/current/theorem_lean_concordance.md` and the per-formula scope notes below.

## Current-source delta review

### D187 (lines 1469–1473)

New display: integer upper/lower tail envelopes with support cutoffs. It uses ceil/floor event identities, and assigns zero when the rounded threshold is outside the support. The actual-law ceiling/floor and two-sided statements are exactly packaged by `ExactHoeffding.manuscript_integer_two_sided_contract` (`ManuscriptIntegerContract.lean`).

### D188 (lines 1475–1477)

New display: the two-sided deviation event is bounded by the smaller of one and the sum of the two one-sided envelopes. Disjoint upper/lower events and the probability cap are part of `ExactHoeffding.manuscript_integer_two_sided_contract` (`ManuscriptIntegerContract.lean`); endpoint cutoffs yield zero mass.

### D197 (lines 1562–1565)

New display: both one-sided Bernstein exponents are strict for positive supported deviations. The proof uses the actual tilted-variance comparison to Bennett and the scalar Bennett-to-Bernstein inequality; the stated upper/lower support intervals are retained. The Lean aggregate is `ExactHoeffding.manuscript_A4_exact_variance_bennett_bernstein_contract` (`ManuscriptA4Contract.lean`).

### D200 (lines 1580–1584)

Edited display: the hypergeometric factorial-moment ratio formula is read with the immediately preceding hypotheses `1 ≤ d ≤ min(k,m)` and `0 ≤ j ≤ d`. Under these conditions all falling-factorial denominators are nonzero; the index range is now stated once in prose and is not dropped mathematically. Exact declaration: `ExactHoeffding.hypergeom_factorial_candidate_formula_of_degree_le_population` (`FactorialChernoffExact.lean`).

### D204 (lines 1607–1612)

New display: the candidate ratio and threshold equivalence hold for `j < d` under the stated strict supported threshold and A-domain. Then `(N−j)(d−j)>0`, and `N+d−k−m>0`; cross multiplication gives `Nd−km−j(N+d−k−m)≥0`. The exact Lean comparison/minimizer chain is `ExactHoeffding.hypergeomFactorialValue_succ_le_iff`, `...index_min`, and the integral-cutoff/endpoint declarations in `FactorialMinimizer.lean`.

## Complete 240-display source binding

| Current display | Source lines | Labels | Display SHA-256 | Review basis | Prior display |
|---|---:|---|---|---|---|
| <a id="display-d1"></a>D1 | 31–36 | — | `0314c4a390502b521a002a71ac79c0576447682d8a2621faf044bfc0c4ff5de2` | exact block in prior audit scope | D1 (line 31) |
| <a id="display-d2"></a>D2 | 46–50 | `eq:exchange-intro` | `68ed7c6b8f3264f2cc32fca2ab48570569ee80c3e95bb40f8cc2c51aed869081` | exact block in prior audit scope | D2 (line 46) |
| <a id="display-d3"></a>D3 | 56–59 | — | `e9997159aa579112a5c176843d39a1064f736fa57a3ccc1644daaccef7897357` | exact block in prior audit scope | D3 (line 56) |
| <a id="display-d4"></a>D4 | 61–64 | — | `14806310f262ca09d9c33906eb892ea45ac20a4e5dcbc3583f86c7adea89479d` | exact block in prior audit scope | D4 (line 61) |
| <a id="display-d5"></a>D5 | 69–72 | — | `552c952fd65c25b9e792ff28c8c752b809745b1934bce705002eabce6a7db89e` | exact block in prior audit scope | D5 (line 69) |
| <a id="display-d6"></a>D6 | 91–94 | `eq:hypergeom` | `aa27b98b9a6f706ef207f2e0fd3bfbe29ae523c5409c72c2f6f20529b23ceac3` | exact block in prior audit scope | D6 (line 88) |
| <a id="display-d7"></a>D7 | 96–99 | `eq:psi` | `f85e0accdafa5ce2420ee38d85c78b241b2f30103c4c2ee4a0a2d8dc90d55e3e` | exact block in prior audit scope | D7 (line 93) |
| <a id="display-d8"></a>D8 | 105–110 | `eq:CNexact` | `99220814f3eb1e64ab82b6117717896ffc9aa230ac0ded659aaf32aaa4fbd4cd` | exact block in prior audit scope | D8 (line 102) |
| <a id="display-d9"></a>D9 | 112–114 | `eq:CNupper` | `2fc303f446b7018c2094c97498cc0d179bc0621e83a8e9673c7d78869d9e9765` | exact block in prior audit scope | D9 (line 109) |
| <a id="display-d10"></a>D10 | 116–118 | `eq:odd_extremizers` | `cd2bd86a4f755d89ffb3d90edcb2093c5ca3e0b98f4f5fc742332e7e8ceee794` | exact block in prior audit scope | D10 (line 113) |
| <a id="display-d11"></a>D11 | 120–122 | `eq:asymptotic` | `8cd29cc8b6de13b7002fb0907074177ab395e464e395bbd6fc1f8f845da419a3` | exact block in prior audit scope | D11 (line 117) |
| <a id="display-d12"></a>D12 | 130–132 | `eq:main_laplace` | `f41020a074601f1cc3d18002f5b8fefc3fb21074d8fb52537649a424b21d27a8` | exact block in prior audit scope | D12 (line 127) |
| <a id="display-d13"></a>D13 | 134–137 | `eq:main_bern_envelope` | `fff2d965ced5c08c0355802b79de5279bdbeb38b2cd1de1fb24290ec9a9a676a` | exact block in prior audit scope | D13 (line 131) |
| <a id="display-d14"></a>D14 | 146–149 | `eq:curvature` | `8fca9641e580c7f6b9b5c4f453ac9fc70fc8627d7eb6cda6279949fa2bdef0b3` | exact block in prior audit scope | D14 (line 143) |
| <a id="display-d15"></a>D15 | 155–158 | `eq:mgf` | `966522a211119e1860f67e2defc8cd0f67e09f005871692ce4cf517a4d1cf6a6` | exact block in prior audit scope | D15 (line 152) |
| <a id="display-d16"></a>D16 | 160–163 | `eq:proxy` | `f0a20c49228fffc7a346917c3984a2ca270bded08e08eaace6451706f0ccdddb` | exact block in prior audit scope | D16 (line 157) |
| <a id="display-d17"></a>D17 | 173–175 | — | `6f5787bf818625cf2c7376ffdb9b1179b27489b917126a1978802f9895e2cf76` | exact block in prior audit scope | D17 (line 170) |
| <a id="display-d18"></a>D18 | 177–180 | — | `2e66018701c9bd0e6c88a72ddc9236e1eadb9615b6879e7292190350c7448491` | exact block in prior audit scope | D18 (line 174) |
| <a id="display-d19"></a>D19 | 182–185 | — | `c7a6475343836e3bf4a1e3b429dbda8121f3d771f6047cae7a75fae5ce7e6a6c` | exact block in prior audit scope | D19 (line 179) |
| <a id="display-d20"></a>D20 | 196–200 | — | `5a5b92129bc80fae1b23ca5ea99b98c599dc8e395587c63735ad96ac17cc2214` | exact block in prior audit scope | D20 (line 193) |
| <a id="display-d21"></a>D21 | 205–208 | — | `9c3f1405f9765503921fd0ae87d5dea684d7cdd5189646aae947706515f2e9cf` | exact block in prior audit scope | D21 (line 202) |
| <a id="display-d22"></a>D22 | 212–215 | — | `05a41fd232aa7e4e84c7ca181af857363b85cf7f1e1625e0ca21029766ecb002` | exact block in prior audit scope | D22 (line 209) |
| <a id="display-d23"></a>D23 | 217–219 | `eq:twolevel_second` | `84283ad0e760788285a8a5b4516e6e85479c94a9a96ed3f908bf446d342d6492` | exact block in prior audit scope | D23 (line 214) |
| <a id="display-d24"></a>D24 | 221–224 | — | `e5e7028671b809e062d9ceba5b02792ab7af11587040083fd0975c9963cc625a` | exact block in prior audit scope | D24 (line 218) |
| <a id="display-d25"></a>D25 | 226–229 | — | `36b5c267d956be8ca28133ff524b1be23ad8b947fe6b5783faa30e2ae9ae46cd` | exact block in prior audit scope | D25 (line 223) |
| <a id="display-d26"></a>D26 | 235–239 | `eq:LKidentity` | `6afe71dfc787d4eb5ed4ba4106af66cd34d832a7e258a9d23a67a1f63025b016` | exact block in prior audit scope | D26 (line 232) |
| <a id="display-d27"></a>D27 | 243–246 | — | `e20bbbfbeb3b74c455cfafd10ab9145251d7e1318ea0e026cb50458d481b355d` | exact block in prior audit scope | D27 (line 240) |
| <a id="display-d28"></a>D28 | 248–251 | — | `c7cf831d9be21fabe2d8af4448b52f6e3559fe92ac2c18c51397160e6a463884` | exact block in prior audit scope | D28 (line 245) |
| <a id="display-d29"></a>D29 | 255–258 | — | `2d828e725bde990185cd6f950d74ef66986be8413498ebd35054eac0ef51e53a` | exact block in prior audit scope | D29 (line 252) |
| <a id="display-d30"></a>D30 | 263–267 | `eq:globalC` | `a988dcd6ca72aeed8d9867c62e28eacbea895221c5361337cbeb32417b8c4cc7` | exact block in prior audit scope | D30 (line 260) |
| <a id="display-d31"></a>D31 | 274–279 | `eq:sym1`, `eq:sym2`, `eq:sym3`, `eq:sym4` | `ff5f4a096b643eb5e489f6ca4501b159b42b379fd4d02a0d710f5976a53b8f4f` | exact block in prior audit scope | D31 (line 271) |
| <a id="display-d32"></a>D32 | 281–284 | `eq:param` | `fce27406ca4b8ace1158fd9d5cd0cb7ae7156d10016107f3b131d8af0fd9c832` | exact block in prior audit scope | D32 (line 278) |
| <a id="display-d33"></a>D33 | 286–288 | `eq:Bdef` | `c21539bbd3115b9e24338e833a65bb2dfed492e41776d63a22a2c1f0caf93144` | exact block in prior audit scope | D33 (line 283) |
| <a id="display-d34"></a>D34 | 293–298 | `eq:Q` | `f216fe51c2d39b5f1d095d24ac847a117fcf66941d8bd3a4e4778fa47ee90095` | exact block in prior audit scope | D34 (line 290) |
| <a id="display-d35"></a>D35 | 300–304 | `eq:tiltuv` | `1b9c46002c4772042b7b25b2cbe044d46e79d5ff414f9f9542a760204ace7e72` | exact block in prior audit scope | D35 (line 297) |
| <a id="display-d36"></a>D36 | 307–310 | `eq:coeffratio` | `52a0610a7acec1dea62336336215552f42357e767302e3a647e92402e9da287c` | exact block in prior audit scope | D36 (line 304) |
| <a id="display-d37"></a>D37 | 312–315 | `eq:hyperode` | `f33a54f4f164b71b75912b6a3a4aadfc7d44338967abe0fd762348a38efe0088` | exact block in prior audit scope | D37 (line 309) |
| <a id="display-d38"></a>D38 | 320–322 | — | `2a9b2c60eb457436b6e4610f1ad35c6bfbe4bd54450291fc9cec5bf2c074d67c` | exact block in prior audit scope | D38 (line 317) |
| <a id="display-d39"></a>D39 | 324–327 | `eq:jacobi` | `c4314cc3e28fd0f4afea2e40b16294b724bda5986cc5df11f6f34a23e886e1aa` | exact block in prior audit scope | D39 (line 321) |
| <a id="display-d40"></a>D40 | 331–333 | `eq:alphas` | `f8ad471ded2948f42f488936693ade74cf0b3124d5d2ab3d6b89bf35902ab848` | exact block in prior audit scope | D40 (line 328) |
| <a id="display-d41"></a>D41 | 335–337 | `eq:factor` | `9d130ecb700bb06f49f9514dcfb247abd3ac9f4751065a0c7cc26760610419f0` | exact block in prior audit scope | D41 (line 332) |
| <a id="display-d42"></a>D42 | 341–343 | `eq:PB` | `ae484f75da22aa7cf301bcfbe7c070a5c6d16e184807ed6a09b621188c0d7335` | exact block in prior audit scope | D42 (line 338) |
| <a id="display-d43"></a>D43 | 347–351 | — | `73c132d29aaf3e6b806173e89ca6933fd6846e3091b6515b14e3738fc4d711d9` | exact block in prior audit scope | D43 (line 344) |
| <a id="display-d44"></a>D44 | 361–363 | `eq:riccati` | `d7cee4ecf41fe6b5908370a58a2da9a922091aff40d283328b068d52939f0fdd` | exact block in prior audit scope | D44 (line 358) |
| <a id="display-d45"></a>D45 | 367–370 | `eq:differentiated` | `815b7f3bfdf9d1b340cbfb316deafdbc9bcdd086497ff3ebb26d7937400c458b` | exact block in prior audit scope | D45 (line 364) |
| <a id="display-d46"></a>D46 | 372–374 | `eq:Dden` | `8da5fadbae691b4a4223191d0a382e0150de94e2471f6faaacdf0ae6ad9a345c` | exact block in prior audit scope | D46 (line 369) |
| <a id="display-d47"></a>D47 | 376–378 | `eq:zfromuv` | `ea708aae3e43c2b02f568654ec0ad066d57a5d2aa57de3e6fb0f288069eb16b2` | exact block in prior audit scope | D47 (line 373) |
| <a id="display-d48"></a>D48 | 380–386 | `eq:F` | `292c624fb203c697d7685f0bda0b1607bcab5070dbaae1f09d0e36db9591a77f` | exact block in prior audit scope | D48 (line 377) |
| <a id="display-d49"></a>D49 | 391–393 | `eq:F0` | `35b17f066235fab78c358de35c1f9a6909a1626c2e9b231294a4d100cfc273f0` | exact block in prior audit scope | D49 (line 388) |
| <a id="display-d50"></a>D50 | 403–405 | `eq:letters` | `ead9efcd867c4f73507bcbb6f318404a1252cc8196d812b6c3a7208d7eea5d92` | exact block in prior audit scope | D50 (line 400) |
| <a id="display-d51"></a>D51 | 407–409 | — | `414ac31218e4b1b95501be7b3f3a1bbbdd4804b06578c65e887277a1275117ba` | exact block in prior audit scope | D51 (line 404) |
| <a id="display-d52"></a>D52 | 411–414 | `eq:AandE` | `629a6d4842529800289890159a52b43e2763da88410c29468b5fc950d7e54e6e` | exact block in prior audit scope | D52 (line 408) |
| <a id="display-d53"></a>D53 | 418–420 | `eq:masterpositive` | `1e00399073bffdba782142cdaf4b1dc58af1cfdf93b9391c94ea0dff0d024d96` | exact block in prior audit scope | D53 (line 415) |
| <a id="display-d54"></a>D54 | 425–427 | — | `c31d984a66832ed5f9553b543d32b0795ab0bb2a7766a18746eb17ea74a46152` | exact block in prior audit scope | D54 (line 422) |
| <a id="display-d55"></a>D55 | 429–431 | `eq:g` | `003cc836b7531a184129ec70336de430d42194561a0ee85033970af6091aa1fa` | exact block in prior audit scope | D55 (line 426) |
| <a id="display-d56"></a>D56 | 436–439 | `eq:square1` | `7806bff64bae045ad525d52cf91917ff37f46f4a8c52134f13b5b54fa42ac2f0` | exact block in prior audit scope | D56 (line 433) |
| <a id="display-d57"></a>D57 | 444–446 | `eq:qmin` | `cfa8e596ff827f75c39613c800b872b724abf7b2891e1821e853ac26e37452da` | exact block in prior audit scope | D57 (line 441) |
| <a id="display-d58"></a>D58 | 448–450 | `eq:qbound` | `18ba9e43274c527259c69c1e6e024fefb77fff6c78eb37e5ceaf28e640a097bb` | exact block in prior audit scope | D58 (line 445) |
| <a id="display-d59"></a>D59 | 452–454 | — | `9cdc2dd976b98649d99bdb5aec8fb53b6d976eae82f20bcde32e5626e3fbef2a` | exact block in prior audit scope | D59 (line 449) |
| <a id="display-d60"></a>D60 | 458–460 | — | `d0df3ae1bb8f5833d7e3f007659cc5719dd7bc6017da3915138e17a29b038df7` | exact block in prior audit scope | D60 (line 455) |
| <a id="display-d61"></a>D61 | 462–465 | — | `8b6d8aee9293cb4e973db486d9e87d83e782e9435657c13e63b3bf28ae042dbd` | exact block in prior audit scope | D61 (line 459) |
| <a id="display-d62"></a>D62 | 467–469 | — | `feb23424a4b86944691df2d66c1cadb1cd0502a3bdcdec6c694d0db912061c92` | exact block in prior audit scope | D62 (line 464) |
| <a id="display-d63"></a>D63 | 471–473 | `eq:gS` | `dddede7f25ef9e055b27a6f56cabc6b63744487cdf862a254c6a38f054e702bb` | exact block in prior audit scope | D63 (line 468) |
| <a id="display-d64"></a>D64 | 475–477 | `eq:Eq` | `d9c3042ec873d3f936e4668fc4836440315fc6eeb63f2cf654537ebeb966dfbb` | exact block in prior audit scope | D64 (line 472) |
| <a id="display-d65"></a>D65 | 479–482 | `eq:Kdef` | `98bb9c6aeeb3bc7cdaacc1d7935ef4cbfd1550d46d821cbd0f7acdd8afa4025c` | exact block in prior audit scope | D65 (line 476) |
| <a id="display-d66"></a>D66 | 484–486 | — | `80080c721a5afc8e81304ccab611d7a497511d473d1eb823363a8a1c7ea80fa7` | exact block in prior audit scope | D66 (line 481) |
| <a id="display-d67"></a>D67 | 488–494 | `eq:Kpositive` | `eee5144196a97ede7d521a99025da283e366610f919756d32358eacab9896086` | exact block in prior audit scope | D67 (line 485) |
| <a id="display-d68"></a>D68 | 506–512 | `eq:exactidentity` | `2faf0bb0a56c17616b8d8fd792f95a412abb987c8018ce65bddeb116f723ee76` | exact block in prior audit scope | D68 (line 503) |
| <a id="display-d69"></a>D69 | 523–525 | `eq:allinner` | `a1646aeaffeb4514929dfa80450e5970d3e734ede2c4c121474c8fadcff53dba` | exact block in prior audit scope | D69 (line 520) |
| <a id="display-d70"></a>D70 | 531–533 | — | `00c04f4f76f5573dc89ac34516c9670a1681cf8f1e67b84d8a0fb0423d883be4` | exact block in prior audit scope | D70 (line 528) |
| <a id="display-d71"></a>D71 | 535–538 | — | `355ed3b074bbe4e22f51e0324a3cdf256ea4d5e99acc02f545909fffcbb6ec47` | exact block in prior audit scope | D71 (line 532) |
| <a id="display-d72"></a>D72 | 540–542 | — | `bc27ddbf330ede3406788f3c49ac5d337d29432f47415c397d936d688ac4db52` | exact block in prior audit scope | D72 (line 537) |
| <a id="display-d73"></a>D73 | 551–554 | — | `a117ed7b340de7efa8d781ae6464137f57ac7ed703b41ee265d3122fa1376155` | exact block in prior audit scope | D73 (line 548) |
| <a id="display-d74"></a>D74 | 556–558 | — | `56bb8c76700f35b740874a706f4b138ba2ada321f1e8e258f4e1caa14eabe13b` | exact block in prior audit scope | D74 (line 553) |
| <a id="display-d75"></a>D75 | 560–563 | — | `dad2bf436cf4dc16d72c0fc78e91db892daf9b2e511870a42dd97b58b6720a80` | exact block in prior audit scope | D75 (line 557) |
| <a id="display-d76"></a>D76 | 566–568 | `eq:3pointvar` | `b77b0694821b0bebaddf2e63a76075ec912a3e103bcde2fe81bf2335229b9188` | exact block in prior audit scope | D76 (line 563) |
| <a id="display-d77"></a>D77 | 570–573 | — | `582168404722065987cd110a11569bd2cf0581b4c1468774bf0413ef96daeadb` | exact block in prior audit scope | D77 (line 567) |
| <a id="display-d78"></a>D78 | 575–579 | — | `d99d83805eef7d6c51ca36d838bbab391173ac86d33ed730149524dc5919cab4` | exact block in prior audit scope | D78 (line 572) |
| <a id="display-d79"></a>D79 | 590–593 | — | `26daa496ff19b41e185d291e0e424541208c17a658423c3c576b8b007a6ffd51` | exact block in prior audit scope | D79 (line 587) |
| <a id="display-d80"></a>D80 | 595–599 | `eq:variance_constant` | `73ae24034e3ad283c945c574a8084853520d47c1b9fbb01919681d69a107d80c` | exact block in prior audit scope | D80 (line 592) |
| <a id="display-d81"></a>D81 | 601–606 | `eq:variance_gap_integral`, `eq:variance_gap_expansion` | `6dcfe9f191c3eb70ad4cba4336646852a53569268bb3eda7b67df418c7694276` | exact block in prior audit scope | D81 (line 598) |
| <a id="display-d82"></a>D82 | 610–614 | — | `0e197439f2a76f994bf3c42ad3ce4fcc6943bbbd09358b4251b59845eac3a2f2` | exact block in prior audit scope | D82 (line 607) |
| <a id="display-d83"></a>D83 | 618–622 | — | `cc69a6146da8d596489adc672e65160db06dfb2a804a5b7857352a0e6a19bbf0` | exact block in prior audit scope | D83 (line 615) |
| <a id="display-d84"></a>D84 | 628–632 | — | `c01d94793dc13b953e4ac64f121ba0ae406ee6d01754d9e1cd6617465e13bf28` | exact block in prior audit scope | D84 (line 625) |
| <a id="display-d85"></a>D85 | 637–641 | — | `99c4b2077c97c52c70d3aeaa8f9c450f941be09296a9e381273c603d4e7e455a` | exact block in prior audit scope | D85 (line 634) |
| <a id="display-d86"></a>D86 | 643–648 | — | `56cf47f41bb3ce21734994b1eea3772118ba710b5da72299b59bc1deed1f1dc2` | exact block in prior audit scope | D86 (line 640) |
| <a id="display-d87"></a>D87 | 652–656 | `eq:bernproxy` | `5c2f29bae1bffd1bca6256e2cb67986f82570ef9c348cc2da906a8a8797ba61c` | exact block in prior audit scope | D87 (line 649) |
| <a id="display-d88"></a>D88 | 658–660 | `eq:oddL` | `baf47cda1e44d540a985cf5f92f048e5d13a50e85f9ab0cf67dad3ad6f412ecf` | exact block in prior audit scope | D88 (line 655) |
| <a id="display-d89"></a>D89 | 672–674 | — | `0341eb0cddb9d38123a0c80ffc180cf9721b4960cbb34e09d20dc3b78df69909` | exact block in prior audit scope | D89 (line 669) |
| <a id="display-d90"></a>D90 | 676–678 | `eq:threeproxy` | `5d4f73cbebad61a519ef96864af0048349379f97206c79f72c69452d640aa8a0` | exact block in prior audit scope | D90 (line 673) |
| <a id="display-d91"></a>D91 | 682–685 | — | `daec0f275bf27d7b7fe1b1fefa93d805bd39910c4e8252f21ebd204e92d7c600` | exact block in prior audit scope | D91 (line 679) |
| <a id="display-d92"></a>D92 | 687–689 | — | `810c9966f6983f66917d5fd2521840260ba8cb708b64bdda72a00c5bb89b069f` | exact block in prior audit scope | D92 (line 684) |
| <a id="display-d93"></a>D93 | 691–693 | — | `a91ac0107300779bcf9afd218cf48e83c7ded946198cdf6d881d7e8431545b66` | exact block in prior audit scope | D93 (line 688) |
| <a id="display-d94"></a>D94 | 699–701 | `eq:Ltwo` | `4766486849d975dc6e000a13e1889ee8f50e36db2001a2933bc633a923f2db37` | exact block in prior audit scope | D94 (line 696) |
| <a id="display-d95"></a>D95 | 703–706 | `eq:twostrict` | `62340074a64994b441d16debf0b83bc382406ca3ed14ab9fced2b353efe1f636` | exact block in prior audit scope | D95 (line 700) |
| <a id="display-d96"></a>D96 | 710–714 | — | `51885e6e339f22e937bbc9e2370b659d07918fd86d0579fe0065d6aa3c12fbdc` | exact block in prior audit scope | D96 (line 707) |
| <a id="display-d97"></a>D97 | 718–721 | — | `5ba4e41116196815684f00d81965f2aedc3d15f6693e9f9887eff5bf90913b94` | exact block in prior audit scope | D97 (line 715) |
| <a id="display-d98"></a>D98 | 723–726 | — | `ff840fac454735cb17affb6ed5a5a6e9a05b5a9bbd064ae1a83524ce0e85abbc` | exact block in prior audit scope | D98 (line 720) |
| <a id="display-d99"></a>D99 | 730–734 | — | `30c28f8f7ff5756a8ea2725bc29b029d8c0a0770b69fa428c2de2c3402bca9dc` | exact block in prior audit scope | D99 (line 727) |
| <a id="display-d100"></a>D100 | 740–743 | — | `2776d9207c80e7c0e1586a7ac57afe56752d2962051f1bfe6c31f0360de28e43` | exact block in prior audit scope | D100 (line 737) |
| <a id="display-d101"></a>D101 | 748–751 | — | `7fba36c52f9c761f792baeaa9d6d0d2c49bed55d00c7476330107678a5b273e6` | exact block in prior audit scope | D101 (line 745) |
| <a id="display-d102"></a>D102 | 754–756 | — | `683c985418ef75e93c7ed686fcaa5ba42d6c02b7612e148b45b0f4b637318853` | exact block in prior audit scope | D102 (line 751) |
| <a id="display-d103"></a>D103 | 758–761 | — | `05ef9b1491d041dd6ccc85e66fdbbb11d8693773d6401f707da30377814510bd` | exact block in prior audit scope | D103 (line 755) |
| <a id="display-d104"></a>D104 | 774–777 | — | `b7ae956b3b5541fd046cff62df677e9f7e67151e5c0c1fa7f329e5e97f83d68f` | exact block in prior audit scope | D104 (line 771) |
| <a id="display-d105"></a>D105 | 779–782 | `odd:eq:laplace` | `901d0c854758168e749c7d7a3cbd6e68691e34f019fd694287e3e42f14ff21c9` | exact block in prior audit scope | D105 (line 776) |
| <a id="display-d106"></a>D106 | 784–788 | `odd:eq:BernEnvelope` | `4c29e3644032b049450e6de4d8a2f6a45adcee543b260ff35ff4a46efbb7735b` | exact block in prior audit scope | D106 (line 781) |
| <a id="display-d107"></a>D107 | 796–798 | — | `b8e5a3095e9e351787c9ce8cca75b2578468cd117820a70c894885ecfce1521e` | exact block in prior audit scope | D107 (line 793) |
| <a id="display-d108"></a>D108 | 800–802 | `odd:eq:variance0` | `0f8bd3139923da06d9f1f969f392b7632e9bd3922ed8cdb96585be93a0760fe8` | exact block in prior audit scope | D108 (line 797) |
| <a id="display-d109"></a>D109 | 806–808 | `odd:eq:PB` | `ccb59b3674e46123688c23c2de3b1e94e58594fd89403b9939a129844d145b1c` | exact block in prior audit scope | D109 (line 803) |
| <a id="display-d110"></a>D110 | 812–815 | — | `997ed1bd5633510299d26adccb1406030985bd8a30887690a45055f307499d55` | exact block in prior audit scope | D110 (line 809) |
| <a id="display-d111"></a>D111 | 819–821 | — | `e797f4f0ffa65208f9e6c63e7566c003967e0eb348c2a4e5456f4746e7959d9d` | exact block in prior audit scope | D111 (line 816) |
| <a id="display-d112"></a>D112 | 823–825 | `odd:eq:F` | `e1f49647b71ab0234f3eb562da5eadb4960adeaec565e44462997adb2e274653` | exact block in prior audit scope | D112 (line 820) |
| <a id="display-d113"></a>D113 | 830–832 | `odd:eq:curveODE` | `0b64bf0f21d62e0b53cb3e0ea1223d5aab4268936bb4279196f8bfeec8bdf677` | exact block in prior audit scope | D113 (line 827) |
| <a id="display-d114"></a>D114 | 836–838 | — | `74f38b62529049c74d7fbc2ec6c7cf0bd117ca7c27896b1732601db93dd639d3` | exact block in prior audit scope | D114 (line 833) |
| <a id="display-d115"></a>D115 | 840–842 | — | `c5507aa1813a5d4914c29768673d0225bf16092cd4390b846272681812dd2265` | exact block in prior audit scope | D115 (line 837) |
| <a id="display-d116"></a>D116 | 844–846 | — | `e67384ebb65700529566b61fc5243883263c35a3e63d4bf409426566863e854d` | exact block in prior audit scope | D116 (line 841) |
| <a id="display-d117"></a>D117 | 852–854 | `odd:eq:P` | `35549bf1d24f2e80878a24bc9031e94f00ed7b80e2d83eb6c5eea0f1aa90dd46` | exact block in prior audit scope | D117 (line 849) |
| <a id="display-d118"></a>D118 | 859–861 | `odd:eq:barrier` | `9dc478d2dda0f97094a9df99b01be0cc82b54d13c8dbc0e2f5d69109f87e1a45` | exact block in prior audit scope | D118 (line 856) |
| <a id="display-d119"></a>D119 | 866–869 | — | `845e52a96ff304e4b80490ad61be36737f5098b0065f4c513034a349554a78b8` | exact block in prior audit scope | D119 (line 863) |
| <a id="display-d120"></a>D120 | 871–873 | `odd:eq:W` | `87f0fcfbe828fd8a7411fc937d38cdf50d2c256bbffd9447b2b3b94e33154178` | exact block in prior audit scope | D120 (line 868) |
| <a id="display-d121"></a>D121 | 875–878 | `odd:eq:residual` | `a9122630a1b55ac9245e6a00cfae2ec0760ba05cf5b213535bb7f166b9c04a2b` | exact block in prior audit scope | D121 (line 872) |
| <a id="display-d122"></a>D122 | 882–887 | — | `01c3163a0d8f86bdc2d8b7a9bb33165572ea70b7d97dc2fc7b3ac68bd7ee4446` | exact block in prior audit scope | D122 (line 879) |
| <a id="display-d123"></a>D123 | 889–891 | `odd:eq:E` | `fc66039727fb8cd680f5efeb9f127bbf360a9e6d2ba570509477613f99248644` | exact block in prior audit scope | D123 (line 886) |
| <a id="display-d124"></a>D124 | 896–899 | `odd:eq:lambda` | `1f73f7490e875d05228c03fd5c63a594f6cccd264d0a97b3a4eae57209245cca` | exact block in prior audit scope | D124 (line 893) |
| <a id="display-d125"></a>D125 | 901–905 | — | `5788ca86519277730290f734b08a1d18a03a901f0bad2f511a3fb210090edee2` | exact block in prior audit scope | D125 (line 898) |
| <a id="display-d126"></a>D126 | 907–911 | `odd:eq:certificate` | `a6c5c1a3998baa0130ddc0cfe695d7df7247a7e96c3c687dabed9273bce1c709` | exact block in prior audit scope | D126 (line 904) |
| <a id="display-d127"></a>D127 | 913–916 | `odd:eq:det` | `de0955cca4af98b3affbd12c7ba801ca113d4ae2fe72c30d231a7fa6507db336` | exact block in prior audit scope | D127 (line 910) |
| <a id="display-d128"></a>D128 | 918–921 | — | `45f82b73ca9d87839a56d6f15af03a3af2e1a0ac15c8c127f9073e48b3e84cd9` | exact block in prior audit scope | D128 (line 915) |
| <a id="display-d129"></a>D129 | 924–926 | — | `17673b6f58cf32e439dfb081dfee9320d557bcf3411c23c8c88396a15ddbe48e` | exact block in prior audit scope | D129 (line 921) |
| <a id="display-d130"></a>D130 | 928–935 | `odd:eq:lambda_pos`, `odd:eq:alpha_pos`, `odd:eq:U_pos`, `odd:eq:V_pos` | `4636931b0c92ecedbc5432874066acaf1f439d775b91d870b6d80be2ad6ea1ba` | exact block in prior audit scope | D130 (line 925) |
| <a id="display-d131"></a>D131 | 938–940 | `odd:eq:Wpositive` | `2d0113e8fc7d8c63fd4a0d086fcfff71b22411d976e8c2408683b82a6360ecd2` | exact block in prior audit scope | D131 (line 935) |
| <a id="display-d132"></a>D132 | 945–950 | `odd:eq:end0`, `odd:eq:endm` | `fd0812386cb72ff6bc693768f78c33e163f0a8912244c59855e694444a253d05` | exact block in prior audit scope | D132 (line 942) |
| <a id="display-d133"></a>D133 | 958–960 | `odd:eq:crossing` | `801aab212daa944d0e1d87b6c7e653c56e0bb8bb62aa3eccdcb273dc9259f154` | exact block in prior audit scope | D133 (line 955) |
| <a id="display-d134"></a>D134 | 969–972 | — | `8f632e5c3b4ccf97ea1b2474406c67ab8a999a20a0ab1e6a20d1b743fddf0353` | exact block in prior audit scope | D134 (line 966) |
| <a id="display-d135"></a>D135 | 975–977 | `odd:eq:Y` | `77e7cd59d40a44e1756b9dfd7e46beea9edab3b3df28c9bb0333c53f507087f8` | exact block in prior audit scope | D135 (line 972) |
| <a id="display-d136"></a>D136 | 979–982 | — | `a1febc96004454435021c7446343cb76729b3549a524811550963557f8de1c7d` | exact block in prior audit scope | D136 (line 976) |
| <a id="display-d137"></a>D137 | 984–987 | — | `05b7417aa91417faf00b693dad37009cf340b7ba7034b777d183b373c5ac654a` | exact block in prior audit scope | D137 (line 981) |
| <a id="display-d138"></a>D138 | 990–993 | — | `170a2baad887018e77adff840ad251561c8ab1265c502d6c06cfd4fad16829ae` | exact block in prior audit scope | D138 (line 987) |
| <a id="display-d139"></a>D139 | 997–1000 | `odd:eq:bern` | `13edd654c3bee15a12760fcf5f75f671d0902a77eeb0c483d1f2b525ea9124f7` | exact block in prior audit scope | D139 (line 994) |
| <a id="display-d140"></a>D140 | 1004–1006 | — | `99ed2f55c5dbf69ff2235dbae12f5053ac475ae4590091a774ad3773fd3cccbc` | exact block in prior audit scope | D140 (line 1001) |
| <a id="display-d141"></a>D141 | 1012–1016 | `odd:eq:exact` | `f0524d9d9eb72ef40ba3cb07d28217537aeaec52aefb425427f08b0502add3a1` | exact block in prior audit scope | D141 (line 1009) |
| <a id="display-d142"></a>D142 | 1023–1026 | — | `58172a9e34ef1b7625379cff6373532f6072f82e706375a9333372635cd8e7cb` | exact block in prior audit scope | D142 (line 1020) |
| <a id="display-d143"></a>D143 | 1030–1034 | — | `827ca4ba5f98f8a5bcbe388b2b3c0d30eca35740842d80d72deddc4b0149c1a9` | exact block in prior audit scope | D143 (line 1027) |
| <a id="display-d144"></a>D144 | 1045–1048 | — | `a307d4df394cd90f7e211ff0927f7147000afe4ff877802caba6918f00160d6a` | exact block in prior audit scope | D144 (line 1042) |
| <a id="display-d145"></a>D145 | 1050–1055 | `eq:rootineq` | `56c020777643fc5916fc024c9eaac1c0e66c3f51c2bcbf8f71913c3250c1e4c2` | exact block in prior audit scope | D145 (line 1047) |
| <a id="display-d146"></a>D146 | 1060–1062 | — | `72085b200e787d6021721e67910f6bad366639826e24bbdbd09341b52d0d57e0` | exact block in prior audit scope | D146 (line 1057) |
| <a id="display-d147"></a>D147 | 1064–1066 | — | `09d4f9c6a8111ffc0146bf532138a2d57b77fa161b2cc264f0d112eda2ede3e8` | exact block in prior audit scope | D147 (line 1061) |
| <a id="display-d148"></a>D148 | 1078–1082 | `B:pmf` | `e5aa0e0d3eb319d53f4f2620376bdcce37e61c59511b082e59a55d106e76b30f` | exact block in prior audit scope | D148 (line 1075) |
| <a id="display-d149"></a>D149 | 1084–1088 | `B:variance` | `3960cc976c3e28814e7338e1efc68ee3e89ec18288bcf3bb1614306ddd4afac5` | exact block in prior audit scope | D149 (line 1081) |
| <a id="display-d150"></a>D150 | 1090–1094 | `B:proxy` | `c90c1f28c71f79c7a690446085c1c9956c84e40d072fc29844d4f5c7c2420247` | exact block in prior audit scope | D150 (line 1087) |
| <a id="display-d151"></a>D151 | 1098–1103 | `B:W` | `5f4200fe97c39ed6d80069105a928def167e2705ab4670876a95b24029d15255` | exact block in prior audit scope | D151 (line 1095) |
| <a id="display-d152"></a>D152 | 1107–1111 | `B:C` | `a99caa652bdc9210593ab7bff2e3000347b01de3ecb6bf6ac92a845ca3713bb0` | exact block in prior audit scope | D152 (line 1104) |
| <a id="display-d153"></a>D153 | 1113–1116 | `B:B` | `f267ccd5297703915e57fb00370927a6dce1c9a6c30cf8b6b2e66b163464fe2c` | exact block in prior audit scope | D153 (line 1110) |
| <a id="display-d154"></a>D154 | 1124–1127 | `B:argmax` | `6bd7faa53d1435ba64b62f7b10493a4ef05aa4cf865f0be834e3fe38ff3ce80b` | exact block in prior audit scope | D154 (line 1121) |
| <a id="display-d155"></a>D155 | 1129–1135 | `B:delta` | `b9550aa47f6b16e6470449161ff12d281a9bbce002d5f5905a077c33721124b2` | exact block in prior audit scope | D155 (line 1126) |
| <a id="display-d156"></a>D156 | 1137–1140 | `B:strict` | `457310e193d452fa5731e0d94b65cc26625197689d8b7d799574f131f3a5c77d` | exact block in prior audit scope | D156 (line 1134) |
| <a id="display-d157"></a>D157 | 1146–1150 | `B:Bdeficit` | `f5c95739836b661b15a6402b1ec63c28f08515edad3871292faea8174b143b5b` | exact block in prior audit scope | D157 (line 1143) |
| <a id="display-d158"></a>D158 | 1167–1169 | `B:cap1` | `a7659f1eb28e9a9cf1e86e9b0825c25eea6b5d43086a482a68ae6e1e09914cdf` | exact block in prior audit scope | D158 (line 1164) |
| <a id="display-d159"></a>D159 | 1172–1176 | — | `cc8744b3b59d1974231e8c6ed8f257bccd2f327e361c8e54ab6af05f7809ee5d` | exact block in prior audit scope | D159 (line 1169) |
| <a id="display-d160"></a>D160 | 1179–1184 | — | `74a4cc2bdda50306acab75968912ce688006667c19d8f7bcd9e49a205deb68c0` | exact block in prior audit scope | D160 (line 1176) |
| <a id="display-d161"></a>D161 | 1188–1191 | `B:cap2` | `2359148eff4d8a103c5c12cf46bd72a4018251172a2406acea407cdbc9e14e30` | exact block in prior audit scope | D161 (line 1185) |
| <a id="display-d162"></a>D162 | 1193–1196 | `B:disc` | `831928b7653c12525f6ffdc92834c52a585843cf723e20caaedede8ec6c66630` | exact block in prior audit scope | D162 (line 1190) |
| <a id="display-d163"></a>D163 | 1199–1202 | — | `d8a63151c57c4dd0765822618983cc8766e7a8ae54affa5a37f336b79d9d5a88` | exact block in prior audit scope | D163 (line 1196) |
| <a id="display-d164"></a>D164 | 1205–1210 | — | `7480b52c241bf29f03777ea66482e0fdc70821a471cc712027c2abada4317028` | exact block in prior audit scope | D164 (line 1202) |
| <a id="display-d165"></a>D165 | 1226–1232 | — | `aa1e662d8da9368f3456dd6cda49fc9ea7a95246792527858491858dee55a1fe` | exact block in prior audit scope | D165 (line 1223) |
| <a id="display-d166"></a>D166 | 1247–1250 | — | `e69e1dcd297d844c9c72d95d899c76f3bb1d0f58d3589bf86bfd00235f336151` | exact block in prior audit scope | D166 (line 1244) |
| <a id="display-d167"></a>D167 | 1261–1263 | — | `5f88210c1e56b72d60cba98553f9978636e9be5232f1bdd1750daa883511fe4f` | exact block in prior audit scope | D167 (line 1258) |
| <a id="display-d168"></a>D168 | 1266–1275 | — | `cb3830c4e00a0365a5b17e1d03f02ef70522774597ca411e127386352ee72234` | exact block in prior audit scope | D168 (line 1263) |
| <a id="display-d169"></a>D169 | 1282–1286 | — | `1cce5d32e3bb39ed3a1c839fbfe85b7f82de7ea9a6baecd1e780c8f4e9adcbab` | exact block in prior audit scope | D169 (line 1279) |
| <a id="display-d170"></a>D170 | 1298–1300 | — | `911f074594fa1b8318de23c6a9b2393f03e27cfdebd4475e804927beaf88e174` | exact block in prior audit scope | D170 (line 1295) |
| <a id="display-d171"></a>D171 | 1302–1304 | — | `97edca3a5f7bdb2d2c612991d51abf572c9a94aff62a0bb154bcc5a8fc7bbf55` | exact block in prior audit scope | D171 (line 1299) |
| <a id="display-d172"></a>D172 | 1319–1321 | `A:domain` | `c265ee7b382efa362f124f5732e6aa855191b263b220322c2cc00cd734f34be9` | exact block in prior audit scope | D172 (line 1316) |
| <a id="display-d173"></a>D173 | 1323–1326 | — | `2378cc03879db090ac4821ae2b69084495e45b4e0a4dfa3056342c54d9af65e4` | exact block in prior audit scope | D173 (line 1320) |
| <a id="display-d174"></a>D174 | 1333–1337 | `A:PB`, `A:barrier` | `cee4003ba4add222af74eb07a9660c58be37560f86b8a6417da1b721eb97bc72` | exact block in prior audit scope | D174 (line 1330) |
| <a id="display-d175"></a>D175 | 1346–1348 | — | `dff3e0b2f2158774995a07e00a354e09fff0c60d9aab070023161a0a46ae83be` | exact block in prior audit scope | D175 (line 1343) |
| <a id="display-d176"></a>D176 | 1358–1364 | — | `dcdd0b0253ec34e73da1d6ef73a7b51a1cb484d73833327867b68c36973975a2` | exact block in prior audit scope | D176 (line 1355) |
| <a id="display-d177"></a>D177 | 1366–1369 | — | `58425780165d1500522d3cba78c40a2b30710ce9a003dec3496ade191045df0c` | exact block in prior audit scope | D177 (line 1363) |
| <a id="display-d178"></a>D178 | 1389–1391 | `A:IP` | `5e40ad7bf74b7a77a7d1bcba8ed4ab4a09f7159521de77c8c619f70ebdfe13c9` | exact block in prior audit scope | D178 (line 1386) |
| <a id="display-d179"></a>D179 | 1394–1397 | — | `baed9f9cca13144110f3d390245f390730570c617b764f026a246411a361e9a1` | exact block in prior audit scope | D179 (line 1391) |
| <a id="display-d180"></a>D180 | 1399–1401 | `A:IB` | `1c2b8c00fc8c9df752728c07d3ee2d11e8d21b7ebb0b473694a42d3bdb3aa4bc` | exact block in prior audit scope | D180 (line 1396) |
| <a id="display-d181"></a>D181 | 1404–1407 | — | `ae5a6c13e9ad1cfb23d56dce82c804d8fda5140b8b4939ed49efc4f2d3f95f1c` | exact block in prior audit scope | D181 (line 1401) |
| <a id="display-d182"></a>D182 | 1415–1418 | — | `0eb652c3be1558890ef2d5f4e72000e26b850c08c470f074bc443f09a2d4cb19` | exact block in prior audit scope | D182 (line 1412) |
| <a id="display-d183"></a>D183 | 1420–1422 | `A:switch` | `b49620329b7d045294435150bef043016830d2ef9462bbd6eafd0c176d6d3095` | exact block in prior audit scope | D183 (line 1417) |
| <a id="display-d184"></a>D184 | 1426–1435 | `A:J` | `b6fb6e7353704792bdea098c82fff9ea423e29a963ff1c2b3bc43cede6606384` | exact block in prior audit scope | D184 (line 1423) |
| <a id="display-d185"></a>D185 | 1438–1440 | `A:strict` | `a8c7112e5e4e8969d8b7877ed336da515335e7707d1c5fe41372b5b7408d7493` | exact block in prior audit scope | D185 (line 1435) |
| <a id="display-d186"></a>D186 | 1446–1449 | — | `b485e09a9b358afdf6562e6bbac40c43a5343cc18afd4f1aa0d819a3848d1c5c` | exact block in prior audit scope | D186 (line 1443) |
| <a id="display-d187"></a>D187 | 1469–1473 | — | `6829d645c44d888738d1ff57549a22392c50dbc9fa379159ec1aaa2fedab6ecf` | new display, delta reviewed | — |
| <a id="display-d188"></a>D188 | 1475–1477 | — | `891f5ac5b446c899eb4e6a628f01cdc925a12711e62341c2de565613f7e5a200` | new display, delta reviewed | — |
| <a id="display-d189"></a>D189 | 1484–1489 | — | `ce20d8ff72908fd83d6faf385839e8a5bf9c2fd00291fef0fbf40c513e4a389b` | exact block in prior audit scope | D187 (line 1477) |
| <a id="display-d190"></a>D190 | 1492–1496 | — | `5e86337f8d6ab991ff959ca6b0a8d335223b8ad8495c9d513c9afb29bf8fd6de` | exact block in prior audit scope | D188 (line 1485) |
| <a id="display-d191"></a>D191 | 1498–1502 | — | `6270e92e13c6e187bace719dc54368f1aef59941fb9dffafdc9358102c28f466` | exact block in prior audit scope | D189 (line 1491) |
| <a id="display-d192"></a>D192 | 1511–1515 | — | `c4463b5d502b3e2c561bc6c51fa7f5b4712feaced1f5ff515d87f32e52965d3f` | exact block in prior audit scope | D190 (line 1504) |
| <a id="display-d193"></a>D193 | 1519–1521 | — | `f1fd16d4143814781b63f7322eb0bf03098b18595d2710d83d1bf6fd97ae8de2` | exact block in prior audit scope | D191 (line 1512) |
| <a id="display-d194"></a>D194 | 1524–1527 | `A:quadratic` | `4cb87e9ad66d0b9f89d11823f44da8e2ab5580fcb03d4521cb5a6a4dca8645b7` | exact block in prior audit scope | D192 (line 1517) |
| <a id="display-d195"></a>D195 | 1539–1543 | — | `6832b3e786f023e8e64e5ecb5d76f471e967b5fbc2cd3b8f4ae1f10834a761dc` | exact block in prior audit scope | D193 (line 1532) |
| <a id="display-d196"></a>D196 | 1555–1558 | — | `a4216bfafcde0eda411f96724e9e540e78a52b253c38c175b6563e025172a62f` | exact block in prior audit scope | D194 (line 1549) |
| <a id="display-d197"></a>D197 | 1562–1565 | — | `5f499b9050080758cdd4958f56aabb6041bd313282a5767f5e48bda2c860461a` | new display, delta reviewed | — |
| <a id="display-d198"></a>D198 | 1571–1573 | — | `1b8c9b3452c82e252f39c2603cc57d4bcd7a7c5e845f240c39706c1c9ad8a44b` | exact block in prior audit scope | D195 (line 1563) |
| <a id="display-d199"></a>D199 | 1575–1578 | — | `c2deb043648fd34e5d7239355ea73f7fa0d34d6ea5fb0350787e5c77c24bfb0d` | exact block in prior audit scope | D196 (line 1567) |
| <a id="display-d200"></a>D200 | 1580–1584 | — | `e8249658bae03255f7b785320f84a40434678cf428003b5f7ad8b5c5f64ad59f` | scope-corrected, re-reviewed | D197 (line 1572) |
| <a id="display-d201"></a>D201 | 1586–1588 | — | `ea5e34565b1bb8bc686e3ef9285c66e7b1c75d56c77f92e2ef608e8d7b390fc0` | exact block in prior audit scope | D198 (line 1578) |
| <a id="display-d202"></a>D202 | 1594–1597 | — | `4b8fcaba5281d393372380105dfeebdca8b193e6b4c79be7f84c7dcdf14db9c7` | exact block in prior audit scope | D199 (line 1586) |
| <a id="display-d203"></a>D203 | 1603–1605 | — | `cc63c740a77f87fd86bc0ff9803711ac3ff5985864c50b405b4ae3d03059f2bf` | exact block in prior audit scope | D200 (line 1596) |
| <a id="display-d204"></a>D204 | 1607–1612 | — | `7204a93851e6bbc2682bd692eae63cf44621a4856a1458a79274afc466962c1f` | new display, delta reviewed | — |
| <a id="display-d205"></a>D205 | 1625–1628 | `eq:oddparams` | `b5159526b51ad554ad498f3704ff61dde3de1445723e05dd201f34238a21cca4` | exact block in prior audit scope | D201 (line 1613) |
| <a id="display-d206"></a>D206 | 1633–1635 | — | `3ed67cabf4d7f574c76a1ccbbdb9db6fa8118e6c5ee7964d574eec988cb87a04` | exact block in prior audit scope | D202 (line 1621) |
| <a id="display-d207"></a>D207 | 1637–1645 | `eq:tiltexp`, `eq:Rexp` | `6fa82b76d86f25ba6ae376af00d31be16f4e3c5834bee841cc1ef8b97c3b0b33` | exact block in prior audit scope | D203 (line 1625) |
| <a id="display-d208"></a>D208 | 1651–1653 | — | `08af5c70d37685f59346170410ed4a19d5ca8d4bfcfbd42f19fb4e284c54ea81` | exact block in prior audit scope | D204 (line 1639) |
| <a id="display-d209"></a>D209 | 1655–1659 | `eq:fixedgap` | `8ccfd93121d477c7070b77aeb6f575985d5d060eca3da8f546a8985d2f95f665` | exact block in prior audit scope | D205 (line 1643) |
| <a id="display-d210"></a>D210 | 1661–1663 | `eq:offs_gap` | `672dc260b82c763b23edcf2e1021ddbb95ddb06d7e0c3911c3a5bae8e7989cdc` | exact block in prior audit scope | D206 (line 1649) |
| <a id="display-d211"></a>D211 | 1671–1676 | — | `0d3b3aa3a15ce2543aa79f38dbee3f44b91656de42d4788b3b10066d41cd4f57` | exact block in prior audit scope | D207 (line 1659) |
| <a id="display-d212"></a>D212 | 1678–1680 | `eq:q0` | `15b8c44fb7b55436a5424587d217266a202329fb04bc3e3ccc06b56ba8f904f8` | exact block in prior audit scope | D208 (line 1666) |
| <a id="display-d213"></a>D213 | 1682–1684 | `eq:qstrict` | `6734482cfa6bea0b90fcebb022524f56b99f8ab01762660d5897398f3811fb51` | exact block in prior audit scope | D209 (line 1670) |
| <a id="display-d214"></a>D214 | 1688–1694 | `eq:Qexpand` | `d6821a15442ee3fedd5e832639245d4f66302d9980316006461a6a09fb9300cc` | exact block in prior audit scope | D210 (line 1676) |
| <a id="display-d215"></a>D215 | 1696–1698 | — | `ee3241a772503676374781914fffd5678ed1d8c277227bed1f50e9901885aa01` | exact block in prior audit scope | D211 (line 1684) |
| <a id="display-d216"></a>D216 | 1700–1703 | — | `d29020ad5ac4f2465b24ff2b606cd058365fa5a5ed0dc2046f005a5f28e6b601` | exact block in prior audit scope | D212 (line 1688) |
| <a id="display-d217"></a>D217 | 1708–1711 | — | `6f32e9a3dc7d905af1249c338e25e86b9fe46b1d71209e3f133197a7d5d6c792` | exact block in prior audit scope | D213 (line 1696) |
| <a id="display-d218"></a>D218 | 1713–1715 | — | `0a5b66ddd9325a72496f42f94e834e4b93dc4163ca472d01e8086ca0ddbb892c` | exact block in prior audit scope | D214 (line 1701) |
| <a id="display-d219"></a>D219 | 1719–1721 | — | `1fe09c630a3df57361ab0863465f06e822e00f06b129a5ee0f5c34247a8e900f` | exact block in prior audit scope | D215 (line 1707) |
| <a id="display-d220"></a>D220 | 1723–1733 | — | `73d9e74422ed6a9079dd55f64e5167c26aba37982e0b0a7ddc023116c11a5b85` | exact block in prior audit scope | D216 (line 1711) |
| <a id="display-d221"></a>D221 | 1737–1740 | `eq:singletonL` | `e07b162d050a82e96ef5cb2d29363a784f929681042d00b8607b1997c4daf30c` | exact block in prior audit scope | D217 (line 1725) |
| <a id="display-d222"></a>D222 | 1753–1757 | `eq:factorial_moments` | `eab72f27e8e2f585b93ff2379021f56f1f92e9aaa317558760d499ffc3037bb0` | exact block in prior audit scope | D218 (line 1741) |
| <a id="display-d223"></a>D223 | 1759–1762 | — | `da26691cd1d94f60cbcf1e600ab931771e9942adb43ef66bbd4a7e25a5ba4cf6` | exact block in prior audit scope | D219 (line 1747) |
| <a id="display-d224"></a>D224 | 1764–1773 | `eq:kappa2exp`, `eq:kappa3exp`, `eq:kappa4exp`, `eq:kappa56exp` | `477cc31c026c1c589b8da80921ec943db6df1cc1744ebec7b06e195a3033c9ba` | exact block in prior audit scope | D220 (line 1752) |
| <a id="display-d225"></a>D225 | 1775–1778 | — | `b4f36726877441912f26c85b1e2fd8dd4effa0ce4f488d882125485c87224f41` | exact block in prior audit scope | D221 (line 1763) |
| <a id="display-d226"></a>D226 | 1780–1787 | `eq:exactk2`, `eq:exactk3` | `909d40c092a84381cfc45b3aba0e8d8ba98a007ec8bac8881e7f254b7adc62ba` | exact block in prior audit scope | D222 (line 1768) |
| <a id="display-d227"></a>D227 | 1789–1791 | — | `65f8e55392488a469d67bf8b2594a986a23b324dd840ff4a267d0f69c999bc25` | exact block in prior audit scope | D223 (line 1777) |
| <a id="display-d228"></a>D228 | 1800–1802 | `eq:explicitF` | `e731cc053151087656424fec52808ffbb3331c578a26d560245159b644b28e62` | exact block in prior audit scope | D224 (line 1788) |
| <a id="display-d229"></a>D229 | 1804–1807 | `eq:bc` | `4e4a83b770a7d3f9e909a05c558785a770a87a8c5a73d4f8440572b2a89e185c` | exact block in prior audit scope | D225 (line 1792) |
| <a id="display-d230"></a>D230 | 1809–1811 | `eq:vplus` | `238706ff009aa3fb05955428ce2feba04c58b1f5861aed57ab4073e0dffa6376` | exact block in prior audit scope | D226 (line 1797) |
| <a id="display-d231"></a>D231 | 1815–1819 | — | `abc0c0ff823a5e16f74cf198f4ba7bc07b5b6b379b16a49431be7a53aa4f47f0` | exact block in prior audit scope | D227 (line 1803) |
| <a id="display-d232"></a>D232 | 1824–1827 | — | `c2b4565987503fb7fc4f695d0556264bd4292c8b1ad48b12d2b259f8019d54be` | exact block in prior audit scope | D228 (line 1812) |
| <a id="display-d233"></a>D233 | 1828–1830 | — | `06de0f91ef05d8134dce67ac69f6f1e27483b2573e84a0d1cb9a95e8a623abfe` | exact block in prior audit scope | D229 (line 1816) |
| <a id="display-d234"></a>D234 | 1832–1835 | — | `ab823717082e5134870aadac61e2971130c75efa8e82cb4abb35c88e3bc6cebd` | exact block in prior audit scope | D230 (line 1820) |
| <a id="display-d235"></a>D235 | 1842–1845 | — | `f2fdccfc739fcabf54fbd9d3e407f1aeba672f7f8432ee34d4a5509af1874dec` | exact block in prior audit scope | D231 (line 1830) |
| <a id="display-d236"></a>D236 | 1847–1849 | — | `8c3057d5c712d4ddd0f8a452e2a6c471366a7894e80a51e718f90927d414c6a2` | exact block in prior audit scope | D232 (line 1835) |
| <a id="display-d237"></a>D237 | 1851–1854 | `eq:bernref` | `72aa9c357637aac15fe4fa3617313a65c720a9b15601edfefb8420f026c2faf2` | exact block in prior audit scope | D233 (line 1839) |
| <a id="display-d238"></a>D238 | 1856–1858 | `eq:bernsecond` | `6c097889198ce3d6b4c372ef640c6791ff2c57eb9b36ebe91b4df5a6434a801a` | exact block in prior audit scope | D234 (line 1844) |
| <a id="display-d239"></a>D239 | 1860–1862 | — | `6ede54a88be7922e164cd61f1a6afdaf009cf79fc79137e33b7d60f0ecc54b6b` | exact block in prior audit scope | D235 (line 1848) |
| <a id="display-d240"></a>D240 | 1866–1870 | — | `7ae70276fcb25bf15d8161a56941354c4ae46602ef6b8aef2d5a8f05f4a5fe81` | exact block in prior audit scope | D236 (line 1854) |
