import YM.QCD.King.Rings
/-! # economics of Gaze brush. factor on both near masks, widen sales. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Kings
open Finset RG Filter Function Lattice Wilson ConnectedActivityE6 Blaze Coat Metric
open Fork Lat Loom Fleet Kit Port Jets Run Brush Tidings Cove Sun Beam Pipe King Eider
open Blaze.Vine Push Push.AbsoluteSums Footprint Pressure Stores Tree SectorMeasure
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator Classical ContDiff
variable {c:Side}{V : Type}[NormedAddCommGroup V][NormedSpace ℝ V]{U:V → Grid c} {x:V}{k b B n:ℕ}{p a η w W:ℝ}
variable {H:St c}{G:Land c (Site c) (Site c)}{Y:Pays c (Site c) (Site c)}{s z ξ Λ μ C:ℝ} {f L:Side}{S:StepData c f}{P:Teller su}{T:Tube su S}{R:Rep su f}
variable {Q:Target su P}{o:Target.Order su W}
variable (J:Cash W s μ L Q o C T R)
open Jets.Touch
-- pos adjusted from local tape. normalized constants
noncomputable def knock (k:ℕ)(η v:ℝ):ℝ:=(k.factorial*(letterP η k))*((1+(massQ+massQ))*v)
def posR (k:ℕ):ℝ:= Real.exp 1*(1+heartQ k)
lemma heartPos (k:ℕ) :0 ≤ heartQ k:=by unfold heartQ; have hh:=let_pos (δ:=1) zero_lt_one k; positivity
lemma pos_bar (k:ℕ) :Real.exp 1≤posR k := le_mul_of_one_le_right (Real.exp_pos _).le (le_add_of_nonneg_right (heartPos ..))
lemma shiftP (hp:0 < z)(ht:z ≤1):∀ u:ℝ, 0 ≤ u →tomato u z k ≤ Real.exp u*(1+heartQ k):=by
   intro u he; unfold tomato; have hh:=heartPos k; nlinarith [mul_le_mul_of_nonneg_left ht hh,mul_pos (Real.exp_pos u) hp,Real.exp_pos u]
lemma smallQ (u a:ℝ)(ha:0≤a)(hh:0≤u)(h:u≤a)(hk:a≤1): tomato a u k≤ posR k*a:=by
   unfold tomato posR; have he:= fastR a ha hk; have ht':0≤heartQ k*u:= mul_nonneg (heartPos k) hh; have hx:=heartPos k; exact (add_le_add he (mul_le_mul (Real.exp_le_exp.mpr hk) (mul_le_mul_of_nonneg_left h hx) ht' (Real.exp_pos _).le)).trans_eq (by ring)
lemma surgeL (h:Pack id id η p b H a G Y)(ht:0<η)(he:0<w)(hi:Gaze c)(hU:Mode U x k z)(V:Grid f) (v u:ℝ)
 (hf: (1+(massQ+massQ))*z ≤1)(hw: knock k η z*gala Y hi (radiusB s) n w ≤ u)(ha:u≤1)(hq: ‖token c n w (dropG n G S.ratio (radiusB s) hi V (U x))‖≤v): Brush k (tomato v u k) 1
    (fun i=>wearK c n w ((sailP J G n).works hi V (U i))) x:=by
   let Z i:= dropG n G S.ratio (radiusB s) hi V (U i)
   have hF : Brush k u 1 (fun i=>wearK c n w (Z i)-wearK c n w (Z x)) x:=by
      apply (fumage (circus h ht (radiusB s) n hi S.ratio V he hU) hf).climb _ le_rfl
      apply le_trans _ hw; unfold knock; exact le_of_eq (by ring)
   refine (swelled (V:=fun i=>wearK c n w (Z i)) hF ha (show _ from hq)).shimmy (Eventually.of_forall fun i=>?_)
   exact (map_sub ..).trans (congr_arg₂ Sub.sub (NormedSpace.map_exp (wearK c n w) (songT (c:=c) (N:=n) w).continuous (Z i)) (map_one _))
set_option maxHeartbeats 450000 in
lemma launchL (h:Pack id id η p b H a G Y)(ht:0 < η)(he:0<w)(hv:0 < p)(hq:0 ≤ z)(Z:ℝ)(M:ℝ → ℝ)(A:ℝ)(χ:Chi)(hp:0< Z)(hs: Woods P L (2*o.a) M s)(d:ℝ)(hd:0< d)(hc:∀ x:su.El,‖colour x-1‖ ≤ d*su.chord x)(hS : L.val+1 ≤ radiusB s)(hm:d*(L.val*M s)<η/2)
 (hR: w^2*fingers n^2*(4*(d*(L.val*M s))/(η/2)*a)≤ Z)(hg:∀ i,glaze Y Z w n (radiusB s) i ≤1) (hD: (1+(massQ+massQ))*z ≤1) (hE:knock k η z ≤1)(hκ : knock k η z*(w^2*fingers n^2*(4*a)) ≤ Z) (hH:Real.exp (max 0 (w^2*fingers n^2*(4*a))) ≤ wear L s*(Real.exp 1*Z)) :
 let S':=sailP J G n; let g i:=posR k*glaze Y Z w n (radiusB s) i;
 Honest S' A 1 (fan L (1/4) s) g w z χ k Prod.fst (univ.filter fun i=>i.2=none) (18*radiusB s) 1:=by
     intro S' g
     have hm':0 ≤ knock k η z:= by
         unfold knock; have hI:=let_pos ht k
         have hp :0 ≤ massQ:=mul_nonneg (norm_nonneg opBox) (zero_le_one.trans (royalty_ge su)); positivity
     let R':=glaze Y Z w n (radiusB s)
     have hv' : 0 ≤ R' := fun i=>by unfold R' glaze; split; exact hp.le; exact galaN h ..
     have hx:0 ≤ g:=fun i=>mul_nonneg ((Real.exp_pos _).le.trans (pos_bar k)) (hv' i)
     have he':=fan_pos L (1/4) s; refine ⟨hx,zero_le_one,he'.le,fun F U ht' hv' hf hU E _ _ _ x V y hu hy i hh=> ?_,?_⟩
     · intro B; have hP:Room P S T U.x:=hf.symm ▸ J.laws.data.room; let m:=radiusB s; let Z':=worldZ U R.beta y; let W₁:=S.ratio; let U':=U.input Z'; let o':=i.1; let s:=gala Y i m n w
       have H': L=S.patch.L:=J.laws.data.funds.length_eq.symm
       have hs': (S.ratio.count.val+1 ≤ m):=by rw [show S.ratio.count=L from H'.symm]; exact hS
       have hz:s≥0:=galaN h ..
       have hX:‖token _ _ w (dropG n G S.ratio m i U' (V x))‖ ≤ s:= galaP h i m n U' (V x) ht he
       have hB:1 ≤ windy S' 1 i:=by
         unfold King.windy; rw [one_mul,Nat.one_le_cast]; refine (Animals.price_pos ..).2 ⟨i.1,?_⟩; apply halo_subset; apply seaP i m S.ratio; exact halo_subset _ _ (mem_singleton_self _)
       by_cases hi:i.2=none
       swap; · have hm : s=R' i:= (if_neg hi).symm; have hf:s ≤1:= hm.trans_le (hg _)
               have hY := surgeL J h ht he i hy U' s s hD (mul_le_of_le_one_left hz hE) hf hX
               have hp:tomato s s k ≤ g i:= (smallQ s s hz hz le_rfl hf).trans_eq (congr_arg _ hm)
               exact ⟨Or.inl (hY.climb hp hB), hY.climb (hp.trans (le_mul_of_one_le_left (hx i) (Real.one_le_exp he'.le))) hB⟩
       rcases i with ⟨i,p⟩; change p=none at hi; subst p; let i':Gaze c:=(i,none)
       have hm0:R' i'=Z:=if_pos rfl; have hI:g i'= posR k*Z:=congr_arg _ hm0
       have hz':= galaSun (X:=H) (a:=w) h i m n hv.le -- signature
       have hu₁:knock k η z*s ≤ Z:= le_trans (mul_le_mul_of_nonneg_left hz' hm') hκ
       have hu₂: Z≤1:= hm0 ▸ hg i'
       have hVR := surgeL J h ht he i' hy U' s Z hD hu₁ hu₂ hX
       refine ⟨?_,hVR.climb ?_ hB⟩
       swap
       · have hh:Real.exp s ≤ wear L (U.x)*(Real.exp 1*Z):=by rw [hf]; exact le_trans (Real.exp_monotone (hz'.trans (le_max_right ..))) hH -- syntax
         rw [hf] at hh; rw [hI]; apply le_trans (shiftP hp hu₂ s hz); unfold posR; unfold wear at hh; apply le_trans (mul_le_mul_of_nonneg_right hh (show 0≤1+ heartQ k by linarith [heartPos k])); exact le_of_eq (by ring)
       by_cases hp:Shell.Inside i U.seeds (18*m)
       · obtain ⟨j,hj,he⟩:=halo_spec.mp hp; refine Or.inr ⟨mem_filter.mpr ⟨mem_univ _,rfl⟩,j,halo_spec.mpr ⟨i, seaP i' m S.ratio (halo_subset _ _ (mem_singleton_self _)), (separation_comm ..).trans_le (he.trans ?_)⟩, hj,he⟩; change 18*m ≤30*m; omega
       obtain ⟨gX,bX,hx⟩:= drapeG hs _ U i Z' hh hf H'.symm hP hv' (seaP i' m S.ratio) hp o.large
       have hI' : ‖token _ _ w (dropG n G W₁ m i' U' (V x))‖≤ Z:= by
          rw [hu]; have hh:=galaSky h i (4*m) n m U Z' _ gX bX d he hv.le ht hx hd.le hc hs.frames (show d * (S.ratio.count.val*M _) < η/2 from (by rw [show S.ratio.count=L from H'.symm]; exact hm)) (by omega)
          refine hh.trans ?_; rw [show S.ratio.count=L from H'.symm]; exact hR
       exact Or.inl ((surgeL J h ht he i' hy U' Z Z hD hu₁ hu₂ hI').climb ((smallQ Z Z ((by assumption : 0<Z)).le (by positivity) le_rfl hu₂).trans_eq hI.symm) hB)
     intro x; rw [Finset.card_le_one]; intro u hu v hv; simp only [mem_filter, mem_univ,true_and] at hu hv; exact Prod.ext (hu.2.trans hv.2.symm) (hu.1.trans hv.1.symm)
end YM.QCD.Kings
