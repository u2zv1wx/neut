@fmt.i32 = constant [3 x i8] c"%d "
declare i32 @printf(i8* noalias nocapture, ...)
declare i8* @malloc(i64)
declare void @free(i8*)
define i64 @main() {
  %fun.2756 = bitcast i8* ()* @state.1113 to i8*
  %cast.2757 = bitcast i8* %fun.2756 to i8* ()*
  %arg.2386 = call i8* %cast.2757()
  %cursor.2759 = bitcast i8* (i8*, i8*)* @lam.2385 to i8*
  %sizeptr.2775 = getelementptr i64, i64* null, i32 0
  %size.2776 = ptrtoint i64* %sizeptr.2775 to i64
  %cursor.2760 = call i8* @malloc(i64 %size.2776)
  %cast.2766 = bitcast i8* %cursor.2760 to {}*
  %sizeptr.2777 = getelementptr i64, i64* null, i32 2
  %size.2778 = ptrtoint i64* %sizeptr.2777 to i64
  %ans.2758 = call i8* @malloc(i64 %size.2778)
  %cast.2761 = bitcast i8* %ans.2758 to {i8*, i8*}*
  %loader.2764 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2761, i32 0, i32 0
  store i8* %cursor.2759, i8** %loader.2764
  %loader.2762 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2761, i32 0, i32 1
  store i8* %cursor.2760, i8** %loader.2762
  %fun.2387 = bitcast i8* %ans.2758 to i8*
  %base.2767 = bitcast i8* %fun.2387 to i8*
  %castedBase.2768 = bitcast i8* %base.2767 to {i8*, i8*}*
  %loader.2774 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2768, i32 0, i32 0
  %down.elim.cls.2388 = load i8*, i8** %loader.2774
  %loader.2773 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2768, i32 0, i32 1
  %down.elim.env.2389 = load i8*, i8** %loader.2773
  %fun.2769 = bitcast i8* %down.elim.cls.2388 to i8*
  %arg.2770 = bitcast i8* %arg.2386 to i8*
  %arg.2771 = bitcast i8* %down.elim.env.2389 to i8*
  %cast.2772 = bitcast i8* %fun.2769 to i8* (i8*, i8*)*
  %tmp.2779 = tail call i8* %cast.2772(i8* %arg.2770, i8* %arg.2771)
  %cast.2780 = ptrtoint i8* %tmp.2779 to i64
  ret i64 %cast.2780
}
define i8* @lam.2284(i8* %A.1115, i8* %env.2283) {
  %base.2752 = bitcast i8* %env.2283 to i8*
  %castedBase.2753 = bitcast i8* %base.2752 to {}*
  %sizeptr.2781 = getelementptr i64, i64* null, i32 0
  %size.2782 = ptrtoint i64* %sizeptr.2781 to i64
  %ans.2754 = call i8* @malloc(i64 %size.2782)
  %cast.2755 = bitcast i8* %ans.2754 to {}*
  ret i8* %ans.2754
}
define i8* @lam.2286(i8* %S.1114, i8* %env.2285) {
  %base.2741 = bitcast i8* %env.2285 to i8*
  %castedBase.2742 = bitcast i8* %base.2741 to {}*
  %cursor.2744 = bitcast i8* (i8*, i8*)* @lam.2284 to i8*
  %sizeptr.2783 = getelementptr i64, i64* null, i32 0
  %size.2784 = ptrtoint i64* %sizeptr.2783 to i64
  %cursor.2745 = call i8* @malloc(i64 %size.2784)
  %cast.2751 = bitcast i8* %cursor.2745 to {}*
  %sizeptr.2785 = getelementptr i64, i64* null, i32 2
  %size.2786 = ptrtoint i64* %sizeptr.2785 to i64
  %ans.2743 = call i8* @malloc(i64 %size.2786)
  %cast.2746 = bitcast i8* %ans.2743 to {i8*, i8*}*
  %loader.2749 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2746, i32 0, i32 0
  store i8* %cursor.2744, i8** %loader.2749
  %loader.2747 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2746, i32 0, i32 1
  store i8* %cursor.2745, i8** %loader.2747
  ret i8* %ans.2743
}
define i8* @state.1113() {
  %cursor.2733 = bitcast i8* (i8*, i8*)* @lam.2286 to i8*
  %sizeptr.2787 = getelementptr i64, i64* null, i32 0
  %size.2788 = ptrtoint i64* %sizeptr.2787 to i64
  %cursor.2734 = call i8* @malloc(i64 %size.2788)
  %cast.2740 = bitcast i8* %cursor.2734 to {}*
  %sizeptr.2789 = getelementptr i64, i64* null, i32 2
  %size.2790 = ptrtoint i64* %sizeptr.2789 to i64
  %ans.2732 = call i8* @malloc(i64 %size.2790)
  %cast.2735 = bitcast i8* %ans.2732 to {i8*, i8*}*
  %loader.2738 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2735, i32 0, i32 0
  store i8* %cursor.2733, i8** %loader.2738
  %loader.2736 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2735, i32 0, i32 1
  store i8* %cursor.2734, i8** %loader.2736
  ret i8* %ans.2732
}
define i8* @lam.2288(i8* %B.1194, i8* %env.2287) {
  %base.2728 = bitcast i8* %env.2287 to i8*
  %castedBase.2729 = bitcast i8* %base.2728 to {}*
  %sizeptr.2791 = getelementptr i64, i64* null, i32 0
  %size.2792 = ptrtoint i64* %sizeptr.2791 to i64
  %ans.2730 = call i8* @malloc(i64 %size.2792)
  %cast.2731 = bitcast i8* %ans.2730 to {}*
  ret i8* %ans.2730
}
define i8* @lam.2290(i8* %A.1193, i8* %env.2289) {
  %base.2717 = bitcast i8* %env.2289 to i8*
  %castedBase.2718 = bitcast i8* %base.2717 to {}*
  %cursor.2720 = bitcast i8* (i8*, i8*)* @lam.2288 to i8*
  %sizeptr.2793 = getelementptr i64, i64* null, i32 0
  %size.2794 = ptrtoint i64* %sizeptr.2793 to i64
  %cursor.2721 = call i8* @malloc(i64 %size.2794)
  %cast.2727 = bitcast i8* %cursor.2721 to {}*
  %sizeptr.2795 = getelementptr i64, i64* null, i32 2
  %size.2796 = ptrtoint i64* %sizeptr.2795 to i64
  %ans.2719 = call i8* @malloc(i64 %size.2796)
  %cast.2722 = bitcast i8* %ans.2719 to {i8*, i8*}*
  %loader.2725 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2722, i32 0, i32 0
  store i8* %cursor.2720, i8** %loader.2725
  %loader.2723 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2722, i32 0, i32 1
  store i8* %cursor.2721, i8** %loader.2723
  ret i8* %ans.2719
}
define i8* @coproduct.1192() {
  %cursor.2709 = bitcast i8* (i8*, i8*)* @lam.2290 to i8*
  %sizeptr.2797 = getelementptr i64, i64* null, i32 0
  %size.2798 = ptrtoint i64* %sizeptr.2797 to i64
  %cursor.2710 = call i8* @malloc(i64 %size.2798)
  %cast.2716 = bitcast i8* %cursor.2710 to {}*
  %sizeptr.2799 = getelementptr i64, i64* null, i32 2
  %size.2800 = ptrtoint i64* %sizeptr.2799 to i64
  %ans.2708 = call i8* @malloc(i64 %size.2800)
  %cast.2711 = bitcast i8* %ans.2708 to {i8*, i8*}*
  %loader.2714 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2711, i32 0, i32 0
  store i8* %cursor.2709, i8** %loader.2714
  %loader.2712 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2711, i32 0, i32 1
  store i8* %cursor.2710, i8** %loader.2712
  ret i8* %ans.2708
}
define i8* @nat.1200(i8* %coproduct.1197) {
  %ans.2685 = bitcast i8* %coproduct.1197 to i8*
  %arg.2295 = bitcast i8* %ans.2685 to i8*
  %fun.2686 = bitcast i8* (i8*)* @nat.1200 to i8*
  %arg.2687 = bitcast i8* %arg.2295 to i8*
  %cast.2688 = bitcast i8* %fun.2686 to i8* (i8*)*
  %arg.2296 = call i8* %cast.2688(i8* %arg.2687)
  %sizeptr.2801 = getelementptr i64, i64* null, i32 0
  %size.2802 = ptrtoint i64* %sizeptr.2801 to i64
  %ans.2689 = call i8* @malloc(i64 %size.2802)
  %cast.2690 = bitcast i8* %ans.2689 to {}*
  %arg.2291 = bitcast i8* %ans.2689 to i8*
  %ans.2691 = bitcast i8* %coproduct.1197 to i8*
  %fun.2292 = bitcast i8* %ans.2691 to i8*
  %base.2692 = bitcast i8* %fun.2292 to i8*
  %castedBase.2693 = bitcast i8* %base.2692 to {i8*, i8*}*
  %loader.2699 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2693, i32 0, i32 0
  %down.elim.cls.2293 = load i8*, i8** %loader.2699
  %loader.2698 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2693, i32 0, i32 1
  %down.elim.env.2294 = load i8*, i8** %loader.2698
  %fun.2694 = bitcast i8* %down.elim.cls.2293 to i8*
  %arg.2695 = bitcast i8* %arg.2291 to i8*
  %arg.2696 = bitcast i8* %down.elim.env.2294 to i8*
  %cast.2697 = bitcast i8* %fun.2694 to i8* (i8*, i8*)*
  %fun.2297 = call i8* %cast.2697(i8* %arg.2695, i8* %arg.2696)
  %base.2700 = bitcast i8* %fun.2297 to i8*
  %castedBase.2701 = bitcast i8* %base.2700 to {i8*, i8*}*
  %loader.2707 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2701, i32 0, i32 0
  %down.elim.cls.2298 = load i8*, i8** %loader.2707
  %loader.2706 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2701, i32 0, i32 1
  %down.elim.env.2299 = load i8*, i8** %loader.2706
  %fun.2702 = bitcast i8* %down.elim.cls.2298 to i8*
  %arg.2703 = bitcast i8* %arg.2296 to i8*
  %arg.2704 = bitcast i8* %down.elim.env.2299 to i8*
  %cast.2705 = bitcast i8* %fun.2702 to i8* (i8*, i8*)*
  %tmp.2803 = tail call i8* %cast.2705(i8* %arg.2703, i8* %arg.2704)
  ret i8* %tmp.2803
}
define i8* @io.1222(i8* %state.1119) {
  %sizeptr.2804 = getelementptr i64, i64* null, i32 0
  %size.2805 = ptrtoint i64* %sizeptr.2804 to i64
  %ans.2674 = call i8* @malloc(i64 %size.2805)
  %cast.2675 = bitcast i8* %ans.2674 to {}*
  %arg.2300 = bitcast i8* %ans.2674 to i8*
  %ans.2676 = bitcast i8* %state.1119 to i8*
  %fun.2301 = bitcast i8* %ans.2676 to i8*
  %base.2677 = bitcast i8* %fun.2301 to i8*
  %castedBase.2678 = bitcast i8* %base.2677 to {i8*, i8*}*
  %loader.2684 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2678, i32 0, i32 0
  %down.elim.cls.2302 = load i8*, i8** %loader.2684
  %loader.2683 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2678, i32 0, i32 1
  %down.elim.env.2303 = load i8*, i8** %loader.2683
  %fun.2679 = bitcast i8* %down.elim.cls.2302 to i8*
  %arg.2680 = bitcast i8* %arg.2300 to i8*
  %arg.2681 = bitcast i8* %down.elim.env.2303 to i8*
  %cast.2682 = bitcast i8* %fun.2679 to i8* (i8*, i8*)*
  %tmp.2806 = tail call i8* %cast.2682(i8* %arg.2680, i8* %arg.2681)
  ret i8* %tmp.2806
}
define i8* @lam.2308(i8* %arg2.2306, i8* %env.2307) {
  %base.2666 = bitcast i8* %env.2307 to i8*
  %castedBase.2667 = bitcast i8* %base.2666 to {i8*}*
  %loader.2673 = getelementptr {i8*}, {i8*}* %castedBase.2667, i32 0, i32 0
  %arg1.2305 = load i8*, i8** %loader.2673
  %arg.2668 = bitcast i8* %arg1.2305 to i8*
  %arg.2669 = bitcast i8* %arg2.2306 to i8*
  %cast.2670 = ptrtoint i8* %arg.2668 to i32
  %cast.2671 = ptrtoint i8* %arg.2669 to i32
  %result.2672 = mul i32 %cast.2670, %cast.2671
  %result.2807 = inttoptr i32 %result.2672 to i8*
  ret i8* %result.2807
}
define i8* @lam.2310(i8* %arg1.2305, i8* %env.2309) {
  %base.2652 = bitcast i8* %env.2309 to i8*
  %castedBase.2653 = bitcast i8* %base.2652 to {}*
  %cursor.2655 = bitcast i8* (i8*, i8*)* @lam.2308 to i8*
  %cursor.2662 = bitcast i8* %arg1.2305 to i8*
  %sizeptr.2808 = getelementptr i64, i64* null, i32 1
  %size.2809 = ptrtoint i64* %sizeptr.2808 to i64
  %cursor.2656 = call i8* @malloc(i64 %size.2809)
  %cast.2663 = bitcast i8* %cursor.2656 to {i8*}*
  %loader.2664 = getelementptr {i8*}, {i8*}* %cast.2663, i32 0, i32 0
  store i8* %cursor.2662, i8** %loader.2664
  %sizeptr.2810 = getelementptr i64, i64* null, i32 2
  %size.2811 = ptrtoint i64* %sizeptr.2810 to i64
  %ans.2654 = call i8* @malloc(i64 %size.2811)
  %cast.2657 = bitcast i8* %ans.2654 to {i8*, i8*}*
  %loader.2660 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2657, i32 0, i32 0
  store i8* %cursor.2655, i8** %loader.2660
  %loader.2658 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2657, i32 0, i32 1
  store i8* %cursor.2656, i8** %loader.2658
  ret i8* %ans.2654
}
define i8* @lam.2318(i8* %arg2.2316, i8* %env.2317) {
  %base.2644 = bitcast i8* %env.2317 to i8*
  %castedBase.2645 = bitcast i8* %base.2644 to {i8*}*
  %loader.2651 = getelementptr {i8*}, {i8*}* %castedBase.2645, i32 0, i32 0
  %arg1.2315 = load i8*, i8** %loader.2651
  %arg.2646 = bitcast i8* %arg1.2315 to i8*
  %arg.2647 = bitcast i8* %arg2.2316 to i8*
  %cast.2648 = ptrtoint i8* %arg.2646 to i32
  %cast.2649 = ptrtoint i8* %arg.2647 to i32
  %result.2650 = sub i32 %cast.2648, %cast.2649
  %result.2812 = inttoptr i32 %result.2650 to i8*
  ret i8* %result.2812
}
define i8* @lam.2320(i8* %arg1.2315, i8* %env.2319) {
  %base.2630 = bitcast i8* %env.2319 to i8*
  %castedBase.2631 = bitcast i8* %base.2630 to {}*
  %cursor.2633 = bitcast i8* (i8*, i8*)* @lam.2318 to i8*
  %cursor.2640 = bitcast i8* %arg1.2315 to i8*
  %sizeptr.2813 = getelementptr i64, i64* null, i32 1
  %size.2814 = ptrtoint i64* %sizeptr.2813 to i64
  %cursor.2634 = call i8* @malloc(i64 %size.2814)
  %cast.2641 = bitcast i8* %cursor.2634 to {i8*}*
  %loader.2642 = getelementptr {i8*}, {i8*}* %cast.2641, i32 0, i32 0
  store i8* %cursor.2640, i8** %loader.2642
  %sizeptr.2815 = getelementptr i64, i64* null, i32 2
  %size.2816 = ptrtoint i64* %sizeptr.2815 to i64
  %ans.2632 = call i8* @malloc(i64 %size.2816)
  %cast.2635 = bitcast i8* %ans.2632 to {i8*, i8*}*
  %loader.2638 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2635, i32 0, i32 0
  store i8* %cursor.2633, i8** %loader.2638
  %loader.2636 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2635, i32 0, i32 1
  store i8* %cursor.2634, i8** %loader.2636
  ret i8* %ans.2632
}
define i8* @lam.2338(i8* %x.1236, i8* %env.2337) {
  %base.2561 = bitcast i8* %env.2337 to i8*
  %castedBase.2562 = bitcast i8* %base.2561 to {}*
  %ans.2563 = bitcast i8* %x.1236 to i8*
  %tmp.2304 = bitcast i8* %ans.2563 to i8*
  %switch.2628 = bitcast i8* %tmp.2304 to i8*
  %cast.2629 = ptrtoint i8* %switch.2628 to i64
  switch i64 %cast.2629, label %default.2817 [i64 1, label %case.2818]
case.2818:
  %ans.2564 = inttoptr i32 1 to i8*
  ret i8* %ans.2564
default.2817:
  %ans.2565 = inttoptr i32 1 to i8*
  %arg.2325 = bitcast i8* %ans.2565 to i8*
  %ans.2566 = bitcast i8* %x.1236 to i8*
  %arg.2321 = bitcast i8* %ans.2566 to i8*
  %cursor.2568 = bitcast i8* (i8*, i8*)* @lam.2320 to i8*
  %sizeptr.2819 = getelementptr i64, i64* null, i32 0
  %size.2820 = ptrtoint i64* %sizeptr.2819 to i64
  %cursor.2569 = call i8* @malloc(i64 %size.2820)
  %cast.2575 = bitcast i8* %cursor.2569 to {}*
  %sizeptr.2821 = getelementptr i64, i64* null, i32 2
  %size.2822 = ptrtoint i64* %sizeptr.2821 to i64
  %ans.2567 = call i8* @malloc(i64 %size.2822)
  %cast.2570 = bitcast i8* %ans.2567 to {i8*, i8*}*
  %loader.2573 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2570, i32 0, i32 0
  store i8* %cursor.2568, i8** %loader.2573
  %loader.2571 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2570, i32 0, i32 1
  store i8* %cursor.2569, i8** %loader.2571
  %fun.2322 = bitcast i8* %ans.2567 to i8*
  %base.2576 = bitcast i8* %fun.2322 to i8*
  %castedBase.2577 = bitcast i8* %base.2576 to {i8*, i8*}*
  %loader.2583 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2577, i32 0, i32 0
  %down.elim.cls.2323 = load i8*, i8** %loader.2583
  %loader.2582 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2577, i32 0, i32 1
  %down.elim.env.2324 = load i8*, i8** %loader.2582
  %fun.2578 = bitcast i8* %down.elim.cls.2323 to i8*
  %arg.2579 = bitcast i8* %arg.2321 to i8*
  %arg.2580 = bitcast i8* %down.elim.env.2324 to i8*
  %cast.2581 = bitcast i8* %fun.2578 to i8* (i8*, i8*)*
  %fun.2326 = call i8* %cast.2581(i8* %arg.2579, i8* %arg.2580)
  %base.2584 = bitcast i8* %fun.2326 to i8*
  %castedBase.2585 = bitcast i8* %base.2584 to {i8*, i8*}*
  %loader.2591 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2585, i32 0, i32 0
  %down.elim.cls.2327 = load i8*, i8** %loader.2591
  %loader.2590 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2585, i32 0, i32 1
  %down.elim.env.2328 = load i8*, i8** %loader.2590
  %fun.2586 = bitcast i8* %down.elim.cls.2327 to i8*
  %arg.2587 = bitcast i8* %arg.2325 to i8*
  %arg.2588 = bitcast i8* %down.elim.env.2328 to i8*
  %cast.2589 = bitcast i8* %fun.2586 to i8* (i8*, i8*)*
  %arg.2329 = call i8* %cast.2589(i8* %arg.2587, i8* %arg.2588)
  %fun.2592 = bitcast i8* ()* @fact.1235 to i8*
  %cast.2593 = bitcast i8* %fun.2592 to i8* ()*
  %fun.2330 = call i8* %cast.2593()
  %base.2594 = bitcast i8* %fun.2330 to i8*
  %castedBase.2595 = bitcast i8* %base.2594 to {i8*, i8*}*
  %loader.2601 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2595, i32 0, i32 0
  %down.elim.cls.2331 = load i8*, i8** %loader.2601
  %loader.2600 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2595, i32 0, i32 1
  %down.elim.env.2332 = load i8*, i8** %loader.2600
  %fun.2596 = bitcast i8* %down.elim.cls.2331 to i8*
  %arg.2597 = bitcast i8* %arg.2329 to i8*
  %arg.2598 = bitcast i8* %down.elim.env.2332 to i8*
  %cast.2599 = bitcast i8* %fun.2596 to i8* (i8*, i8*)*
  %arg.2333 = call i8* %cast.2599(i8* %arg.2597, i8* %arg.2598)
  %ans.2602 = bitcast i8* %x.1236 to i8*
  %arg.2311 = bitcast i8* %ans.2602 to i8*
  %cursor.2604 = bitcast i8* (i8*, i8*)* @lam.2310 to i8*
  %sizeptr.2823 = getelementptr i64, i64* null, i32 0
  %size.2824 = ptrtoint i64* %sizeptr.2823 to i64
  %cursor.2605 = call i8* @malloc(i64 %size.2824)
  %cast.2611 = bitcast i8* %cursor.2605 to {}*
  %sizeptr.2825 = getelementptr i64, i64* null, i32 2
  %size.2826 = ptrtoint i64* %sizeptr.2825 to i64
  %ans.2603 = call i8* @malloc(i64 %size.2826)
  %cast.2606 = bitcast i8* %ans.2603 to {i8*, i8*}*
  %loader.2609 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2606, i32 0, i32 0
  store i8* %cursor.2604, i8** %loader.2609
  %loader.2607 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2606, i32 0, i32 1
  store i8* %cursor.2605, i8** %loader.2607
  %fun.2312 = bitcast i8* %ans.2603 to i8*
  %base.2612 = bitcast i8* %fun.2312 to i8*
  %castedBase.2613 = bitcast i8* %base.2612 to {i8*, i8*}*
  %loader.2619 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2613, i32 0, i32 0
  %down.elim.cls.2313 = load i8*, i8** %loader.2619
  %loader.2618 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2613, i32 0, i32 1
  %down.elim.env.2314 = load i8*, i8** %loader.2618
  %fun.2614 = bitcast i8* %down.elim.cls.2313 to i8*
  %arg.2615 = bitcast i8* %arg.2311 to i8*
  %arg.2616 = bitcast i8* %down.elim.env.2314 to i8*
  %cast.2617 = bitcast i8* %fun.2614 to i8* (i8*, i8*)*
  %fun.2334 = call i8* %cast.2617(i8* %arg.2615, i8* %arg.2616)
  %base.2620 = bitcast i8* %fun.2334 to i8*
  %castedBase.2621 = bitcast i8* %base.2620 to {i8*, i8*}*
  %loader.2627 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2621, i32 0, i32 0
  %down.elim.cls.2335 = load i8*, i8** %loader.2627
  %loader.2626 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2621, i32 0, i32 1
  %down.elim.env.2336 = load i8*, i8** %loader.2626
  %fun.2622 = bitcast i8* %down.elim.cls.2335 to i8*
  %arg.2623 = bitcast i8* %arg.2333 to i8*
  %arg.2624 = bitcast i8* %down.elim.env.2336 to i8*
  %cast.2625 = bitcast i8* %fun.2622 to i8* (i8*, i8*)*
  %tmp.2827 = tail call i8* %cast.2625(i8* %arg.2623, i8* %arg.2624)
  ret i8* %tmp.2827
}
define i8* @fact.1235() {
  %cursor.2553 = bitcast i8* (i8*, i8*)* @lam.2338 to i8*
  %sizeptr.2828 = getelementptr i64, i64* null, i32 0
  %size.2829 = ptrtoint i64* %sizeptr.2828 to i64
  %cursor.2554 = call i8* @malloc(i64 %size.2829)
  %cast.2560 = bitcast i8* %cursor.2554 to {}*
  %sizeptr.2830 = getelementptr i64, i64* null, i32 2
  %size.2831 = ptrtoint i64* %sizeptr.2830 to i64
  %ans.2552 = call i8* @malloc(i64 %size.2831)
  %cast.2555 = bitcast i8* %ans.2552 to {i8*, i8*}*
  %loader.2558 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2555, i32 0, i32 0
  store i8* %cursor.2553, i8** %loader.2558
  %loader.2556 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2555, i32 0, i32 1
  store i8* %cursor.2554, i8** %loader.2556
  ret i8* %ans.2552
}
define i8* @lam.2341(i8* %arg.2339, i8* %env.2340) {
  %base.2548 = bitcast i8* %env.2340 to i8*
  %castedBase.2549 = bitcast i8* %base.2548 to {}*
  %arg.2550 = bitcast i8* %arg.2339 to i8*
  %cast.2551 = ptrtoint i8* %arg.2550 to i32
  %fmt.2833 = getelementptr [3 x i8], [3 x i8]* @fmt.i32, i32 0, i32 0
  %tmp.2834 = call i32 (i8*, ...) @printf(i8* %fmt.2833, i32 %cast.2551)
  %result.2832 = inttoptr i32 %tmp.2834 to i8*
  ret i8* %result.2832
}
define i8* @lam.2351(i8* %fact.1237, i8* %env.2350) {
  %base.2519 = bitcast i8* %env.2350 to i8*
  %castedBase.2520 = bitcast i8* %base.2519 to {}*
  %ans.2521 = inttoptr i32 10 to i8*
  %arg.2342 = bitcast i8* %ans.2521 to i8*
  %ans.2522 = bitcast i8* %fact.1237 to i8*
  %fun.2343 = bitcast i8* %ans.2522 to i8*
  %base.2523 = bitcast i8* %fun.2343 to i8*
  %castedBase.2524 = bitcast i8* %base.2523 to {i8*, i8*}*
  %loader.2530 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2524, i32 0, i32 0
  %down.elim.cls.2344 = load i8*, i8** %loader.2530
  %loader.2529 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2524, i32 0, i32 1
  %down.elim.env.2345 = load i8*, i8** %loader.2529
  %fun.2525 = bitcast i8* %down.elim.cls.2344 to i8*
  %arg.2526 = bitcast i8* %arg.2342 to i8*
  %arg.2527 = bitcast i8* %down.elim.env.2345 to i8*
  %cast.2528 = bitcast i8* %fun.2525 to i8* (i8*, i8*)*
  %arg.2346 = call i8* %cast.2528(i8* %arg.2526, i8* %arg.2527)
  %cursor.2532 = bitcast i8* (i8*, i8*)* @lam.2341 to i8*
  %sizeptr.2835 = getelementptr i64, i64* null, i32 0
  %size.2836 = ptrtoint i64* %sizeptr.2835 to i64
  %cursor.2533 = call i8* @malloc(i64 %size.2836)
  %cast.2539 = bitcast i8* %cursor.2533 to {}*
  %sizeptr.2837 = getelementptr i64, i64* null, i32 2
  %size.2838 = ptrtoint i64* %sizeptr.2837 to i64
  %ans.2531 = call i8* @malloc(i64 %size.2838)
  %cast.2534 = bitcast i8* %ans.2531 to {i8*, i8*}*
  %loader.2537 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2534, i32 0, i32 0
  store i8* %cursor.2532, i8** %loader.2537
  %loader.2535 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2534, i32 0, i32 1
  store i8* %cursor.2533, i8** %loader.2535
  %fun.2347 = bitcast i8* %ans.2531 to i8*
  %base.2540 = bitcast i8* %fun.2347 to i8*
  %castedBase.2541 = bitcast i8* %base.2540 to {i8*, i8*}*
  %loader.2547 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2541, i32 0, i32 0
  %down.elim.cls.2348 = load i8*, i8** %loader.2547
  %loader.2546 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2541, i32 0, i32 1
  %down.elim.env.2349 = load i8*, i8** %loader.2546
  %fun.2542 = bitcast i8* %down.elim.cls.2348 to i8*
  %arg.2543 = bitcast i8* %arg.2346 to i8*
  %arg.2544 = bitcast i8* %down.elim.env.2349 to i8*
  %cast.2545 = bitcast i8* %fun.2542 to i8* (i8*, i8*)*
  %tmp.2839 = tail call i8* %cast.2545(i8* %arg.2543, i8* %arg.2544)
  ret i8* %tmp.2839
}
define i8* @lam.2357(i8* %io.1223, i8* %env.2356) {
  %base.2498 = bitcast i8* %env.2356 to i8*
  %castedBase.2499 = bitcast i8* %base.2498 to {}*
  %fun.2500 = bitcast i8* ()* @fact.1235 to i8*
  %cast.2501 = bitcast i8* %fun.2500 to i8* ()*
  %arg.2352 = call i8* %cast.2501()
  %cursor.2503 = bitcast i8* (i8*, i8*)* @lam.2351 to i8*
  %sizeptr.2840 = getelementptr i64, i64* null, i32 0
  %size.2841 = ptrtoint i64* %sizeptr.2840 to i64
  %cursor.2504 = call i8* @malloc(i64 %size.2841)
  %cast.2510 = bitcast i8* %cursor.2504 to {}*
  %sizeptr.2842 = getelementptr i64, i64* null, i32 2
  %size.2843 = ptrtoint i64* %sizeptr.2842 to i64
  %ans.2502 = call i8* @malloc(i64 %size.2843)
  %cast.2505 = bitcast i8* %ans.2502 to {i8*, i8*}*
  %loader.2508 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2505, i32 0, i32 0
  store i8* %cursor.2503, i8** %loader.2508
  %loader.2506 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2505, i32 0, i32 1
  store i8* %cursor.2504, i8** %loader.2506
  %fun.2353 = bitcast i8* %ans.2502 to i8*
  %base.2511 = bitcast i8* %fun.2353 to i8*
  %castedBase.2512 = bitcast i8* %base.2511 to {i8*, i8*}*
  %loader.2518 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2512, i32 0, i32 0
  %down.elim.cls.2354 = load i8*, i8** %loader.2518
  %loader.2517 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2512, i32 0, i32 1
  %down.elim.env.2355 = load i8*, i8** %loader.2517
  %fun.2513 = bitcast i8* %down.elim.cls.2354 to i8*
  %arg.2514 = bitcast i8* %arg.2352 to i8*
  %arg.2515 = bitcast i8* %down.elim.env.2355 to i8*
  %cast.2516 = bitcast i8* %fun.2513 to i8* (i8*, i8*)*
  %tmp.2844 = tail call i8* %cast.2516(i8* %arg.2514, i8* %arg.2515)
  ret i8* %tmp.2844
}
define i8* @lam.2364(i8* %zero.1202, i8* %env.2363) {
  %base.2474 = bitcast i8* %env.2363 to i8*
  %castedBase.2475 = bitcast i8* %base.2474 to {i8*}*
  %loader.2497 = getelementptr {i8*}, {i8*}* %castedBase.2475, i32 0, i32 0
  %state.1119 = load i8*, i8** %loader.2497
  %ans.2476 = bitcast i8* %state.1119 to i8*
  %arg.2358 = bitcast i8* %ans.2476 to i8*
  %fun.2477 = bitcast i8* (i8*)* @io.1222 to i8*
  %arg.2478 = bitcast i8* %arg.2358 to i8*
  %cast.2479 = bitcast i8* %fun.2477 to i8* (i8*)*
  %arg.2359 = call i8* %cast.2479(i8* %arg.2478)
  %cursor.2481 = bitcast i8* (i8*, i8*)* @lam.2357 to i8*
  %sizeptr.2845 = getelementptr i64, i64* null, i32 0
  %size.2846 = ptrtoint i64* %sizeptr.2845 to i64
  %cursor.2482 = call i8* @malloc(i64 %size.2846)
  %cast.2488 = bitcast i8* %cursor.2482 to {}*
  %sizeptr.2847 = getelementptr i64, i64* null, i32 2
  %size.2848 = ptrtoint i64* %sizeptr.2847 to i64
  %ans.2480 = call i8* @malloc(i64 %size.2848)
  %cast.2483 = bitcast i8* %ans.2480 to {i8*, i8*}*
  %loader.2486 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2483, i32 0, i32 0
  store i8* %cursor.2481, i8** %loader.2486
  %loader.2484 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2483, i32 0, i32 1
  store i8* %cursor.2482, i8** %loader.2484
  %fun.2360 = bitcast i8* %ans.2480 to i8*
  %base.2489 = bitcast i8* %fun.2360 to i8*
  %castedBase.2490 = bitcast i8* %base.2489 to {i8*, i8*}*
  %loader.2496 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2490, i32 0, i32 0
  %down.elim.cls.2361 = load i8*, i8** %loader.2496
  %loader.2495 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2490, i32 0, i32 1
  %down.elim.env.2362 = load i8*, i8** %loader.2495
  %fun.2491 = bitcast i8* %down.elim.cls.2361 to i8*
  %arg.2492 = bitcast i8* %arg.2359 to i8*
  %arg.2493 = bitcast i8* %down.elim.env.2362 to i8*
  %cast.2494 = bitcast i8* %fun.2491 to i8* (i8*, i8*)*
  %tmp.2849 = tail call i8* %cast.2494(i8* %arg.2492, i8* %arg.2493)
  ret i8* %tmp.2849
}
define i8* @lam.2372(i8* %nat.1201, i8* %env.2371) {
  %base.2441 = bitcast i8* %env.2371 to i8*
  %castedBase.2442 = bitcast i8* %base.2441 to {i8*}*
  %loader.2473 = getelementptr {i8*}, {i8*}* %castedBase.2442, i32 0, i32 0
  %state.1119 = load i8*, i8** %loader.2473
  %ans.2443 = inttoptr i64 0 to i8*
  %sigma.2365 = bitcast i8* %ans.2443 to i8*
  %ans.2444 = inttoptr i64 0 to i8*
  %sigma.2366 = bitcast i8* %ans.2444 to i8*
  %cursor.2446 = bitcast i8* %sigma.2365 to i8*
  %cursor.2447 = bitcast i8* %sigma.2366 to i8*
  %sizeptr.2850 = getelementptr i64, i64* null, i32 2
  %size.2851 = ptrtoint i64* %sizeptr.2850 to i64
  %ans.2445 = call i8* @malloc(i64 %size.2851)
  %cast.2448 = bitcast i8* %ans.2445 to {i8*, i8*}*
  %loader.2451 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2448, i32 0, i32 0
  store i8* %cursor.2446, i8** %loader.2451
  %loader.2449 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2448, i32 0, i32 1
  store i8* %cursor.2447, i8** %loader.2449
  %arg.2367 = bitcast i8* %ans.2445 to i8*
  %cursor.2454 = bitcast i8* (i8*, i8*)* @lam.2364 to i8*
  %cursor.2461 = bitcast i8* %state.1119 to i8*
  %sizeptr.2852 = getelementptr i64, i64* null, i32 1
  %size.2853 = ptrtoint i64* %sizeptr.2852 to i64
  %cursor.2455 = call i8* @malloc(i64 %size.2853)
  %cast.2462 = bitcast i8* %cursor.2455 to {i8*}*
  %loader.2463 = getelementptr {i8*}, {i8*}* %cast.2462, i32 0, i32 0
  store i8* %cursor.2461, i8** %loader.2463
  %sizeptr.2854 = getelementptr i64, i64* null, i32 2
  %size.2855 = ptrtoint i64* %sizeptr.2854 to i64
  %ans.2453 = call i8* @malloc(i64 %size.2855)
  %cast.2456 = bitcast i8* %ans.2453 to {i8*, i8*}*
  %loader.2459 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2456, i32 0, i32 0
  store i8* %cursor.2454, i8** %loader.2459
  %loader.2457 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2456, i32 0, i32 1
  store i8* %cursor.2455, i8** %loader.2457
  %fun.2368 = bitcast i8* %ans.2453 to i8*
  %base.2465 = bitcast i8* %fun.2368 to i8*
  %castedBase.2466 = bitcast i8* %base.2465 to {i8*, i8*}*
  %loader.2472 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2466, i32 0, i32 0
  %down.elim.cls.2369 = load i8*, i8** %loader.2472
  %loader.2471 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2466, i32 0, i32 1
  %down.elim.env.2370 = load i8*, i8** %loader.2471
  %fun.2467 = bitcast i8* %down.elim.cls.2369 to i8*
  %arg.2468 = bitcast i8* %arg.2367 to i8*
  %arg.2469 = bitcast i8* %down.elim.env.2370 to i8*
  %cast.2470 = bitcast i8* %fun.2467 to i8* (i8*, i8*)*
  %tmp.2856 = tail call i8* %cast.2470(i8* %arg.2468, i8* %arg.2469)
  ret i8* %tmp.2856
}
define i8* @lam.2379(i8* %coproduct.1197, i8* %env.2378) {
  %base.2414 = bitcast i8* %env.2378 to i8*
  %castedBase.2415 = bitcast i8* %base.2414 to {i8*}*
  %loader.2440 = getelementptr {i8*}, {i8*}* %castedBase.2415, i32 0, i32 0
  %state.1119 = load i8*, i8** %loader.2440
  %ans.2416 = bitcast i8* %coproduct.1197 to i8*
  %arg.2373 = bitcast i8* %ans.2416 to i8*
  %fun.2417 = bitcast i8* (i8*)* @nat.1200 to i8*
  %arg.2418 = bitcast i8* %arg.2373 to i8*
  %cast.2419 = bitcast i8* %fun.2417 to i8* (i8*)*
  %arg.2374 = call i8* %cast.2419(i8* %arg.2418)
  %cursor.2421 = bitcast i8* (i8*, i8*)* @lam.2372 to i8*
  %cursor.2428 = bitcast i8* %state.1119 to i8*
  %sizeptr.2857 = getelementptr i64, i64* null, i32 1
  %size.2858 = ptrtoint i64* %sizeptr.2857 to i64
  %cursor.2422 = call i8* @malloc(i64 %size.2858)
  %cast.2429 = bitcast i8* %cursor.2422 to {i8*}*
  %loader.2430 = getelementptr {i8*}, {i8*}* %cast.2429, i32 0, i32 0
  store i8* %cursor.2428, i8** %loader.2430
  %sizeptr.2859 = getelementptr i64, i64* null, i32 2
  %size.2860 = ptrtoint i64* %sizeptr.2859 to i64
  %ans.2420 = call i8* @malloc(i64 %size.2860)
  %cast.2423 = bitcast i8* %ans.2420 to {i8*, i8*}*
  %loader.2426 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2423, i32 0, i32 0
  store i8* %cursor.2421, i8** %loader.2426
  %loader.2424 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2423, i32 0, i32 1
  store i8* %cursor.2422, i8** %loader.2424
  %fun.2375 = bitcast i8* %ans.2420 to i8*
  %base.2432 = bitcast i8* %fun.2375 to i8*
  %castedBase.2433 = bitcast i8* %base.2432 to {i8*, i8*}*
  %loader.2439 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2433, i32 0, i32 0
  %down.elim.cls.2376 = load i8*, i8** %loader.2439
  %loader.2438 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2433, i32 0, i32 1
  %down.elim.env.2377 = load i8*, i8** %loader.2438
  %fun.2434 = bitcast i8* %down.elim.cls.2376 to i8*
  %arg.2435 = bitcast i8* %arg.2374 to i8*
  %arg.2436 = bitcast i8* %down.elim.env.2377 to i8*
  %cast.2437 = bitcast i8* %fun.2434 to i8* (i8*, i8*)*
  %tmp.2861 = tail call i8* %cast.2437(i8* %arg.2435, i8* %arg.2436)
  ret i8* %tmp.2861
}
define i8* @lam.2385(i8* %state.1119, i8* %env.2384) {
  %base.2390 = bitcast i8* %env.2384 to i8*
  %castedBase.2391 = bitcast i8* %base.2390 to {}*
  %fun.2392 = bitcast i8* ()* @coproduct.1192 to i8*
  %cast.2393 = bitcast i8* %fun.2392 to i8* ()*
  %arg.2380 = call i8* %cast.2393()
  %cursor.2395 = bitcast i8* (i8*, i8*)* @lam.2379 to i8*
  %cursor.2402 = bitcast i8* %state.1119 to i8*
  %sizeptr.2862 = getelementptr i64, i64* null, i32 1
  %size.2863 = ptrtoint i64* %sizeptr.2862 to i64
  %cursor.2396 = call i8* @malloc(i64 %size.2863)
  %cast.2403 = bitcast i8* %cursor.2396 to {i8*}*
  %loader.2404 = getelementptr {i8*}, {i8*}* %cast.2403, i32 0, i32 0
  store i8* %cursor.2402, i8** %loader.2404
  %sizeptr.2864 = getelementptr i64, i64* null, i32 2
  %size.2865 = ptrtoint i64* %sizeptr.2864 to i64
  %ans.2394 = call i8* @malloc(i64 %size.2865)
  %cast.2397 = bitcast i8* %ans.2394 to {i8*, i8*}*
  %loader.2400 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2397, i32 0, i32 0
  store i8* %cursor.2395, i8** %loader.2400
  %loader.2398 = getelementptr {i8*, i8*}, {i8*, i8*}* %cast.2397, i32 0, i32 1
  store i8* %cursor.2396, i8** %loader.2398
  %fun.2381 = bitcast i8* %ans.2394 to i8*
  %base.2406 = bitcast i8* %fun.2381 to i8*
  %castedBase.2407 = bitcast i8* %base.2406 to {i8*, i8*}*
  %loader.2413 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2407, i32 0, i32 0
  %down.elim.cls.2382 = load i8*, i8** %loader.2413
  %loader.2412 = getelementptr {i8*, i8*}, {i8*, i8*}* %castedBase.2407, i32 0, i32 1
  %down.elim.env.2383 = load i8*, i8** %loader.2412
  %fun.2408 = bitcast i8* %down.elim.cls.2382 to i8*
  %arg.2409 = bitcast i8* %arg.2380 to i8*
  %arg.2410 = bitcast i8* %down.elim.env.2383 to i8*
  %cast.2411 = bitcast i8* %fun.2408 to i8* (i8*, i8*)*
  %tmp.2866 = tail call i8* %cast.2411(i8* %arg.2409, i8* %arg.2410)
  ret i8* %tmp.2866
}