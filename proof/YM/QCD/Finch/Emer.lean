import YM.QCD.Finch.Flux
/-! # Dirac stencil and mass relevant alias at the kinetic station -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Finch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f L :Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove Entr YM.Next.Free Bloch Laurent QCD.Free
open Garden Para
variable {t s τ u :ℝ}{j k:ℕ}{B:BudgetPoint}
open Pearl Metric
section rays
abbrev cocoa (L:Side)(j k:ℕ):= {P:Flight j k//P.L=L}
noncomputable def zerov (n:Side):=tuning (0:Site n)
lemma mount : Tendsto zerov atTop (𝓝 0):=by
    let s n:=Pearl.trek n • trackV 0; have he:Tendsto s atTop (𝓝 0):=by have hh: Tendsto s atTop (𝓝 ((0:ℂ) • trackV 0)) := (advance_0.mono_right nhdsWithin_le_nhds).smul tendsto_const_nhds; simpa using hh
    apply he.congr; intro i; unfold zerov s; funext k; simp only [tuning,menu, trackV, Pi.smul_apply,smul_eq_mul, spacer,Pearl.trek, Complex.ofReal_mul]; rw [show lift (0:Site i)= (0:Cover) from ?_] ; ext; simp [lift]
lemma bring (s:I→ Momentum→ℂ)(hp: Moderate (fun _:I=>1) s) (L:Side → I): Tendsto (fun i:Side=> s (L i) (zerov i)-s (L i) 0) atTop (𝓝 0) :=by
      apply Metric.tendsto_nhds.mpr; intro v hv; obtain ⟨p,a,h,hx,hK⟩:= Flume.motions hp hv
      filter_upwards [Metric.tendsto_nhds.mp mount a hx] with i hi; rw [dist_zero_right]; exact hK (L i) 0 _ (cube_zero _ h) hi
lemma stock (n:Side)(F:Flight j k)(h: F.L=n) (z: Site n) : song F 0 (cast (by rw [h] : Site n=Site F.L) z)= if z=0 then ((n.val:ℂ)* (Kit.slope n:ℂ)) • 1 else 0:=by
    subst n; unfold song; simp only [cast_eq, priceH]; split_ifs <;> simp
lemma spin (D:Side→cocoa L j k) (e:∀ i,(D i).val.L=L)(hp:4 ≤ j)(hv:4 ≤ k): Tendsto (fun i:Side=> Quixote (D i).val (zerov i) chad chad) atTop (𝓝 (L.val:ℂ)):=by
     let s (i):=(Equiv.cast (by rw [e i] : Site L= Site (D i).val.L)); let Φ (p:Site L)(x:Momentum)(i):=song (D i).val x (s i p); let A(p:Site L):Bundle:= if p=0 then ((L.val:ℂ)* (Kit.slope L:ℂ)) • 1 else 0
     have hh(p i): Φ p 0 i=A p:=stock L _ (e i) p
     have hc (p:Site L): Tendsto (fun i=> Φ p (zerov i) i) atTop (𝓝 (A p)):=by
           let Y i(u v: Lat.Fiber):=Φ p (zerov i) i u v -- Fiber conflict
           let H: (Lat.Fiber→ Lat.Fiber→ℂ) →L[ℂ] Bundle:= LinearMap.toContinuousLinearMap { toFun:= fun j=>Matrix.of j,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
           suffices he:Tendsto Y atTop (𝓝 (fun i j=>A p i j)) from H.continuous.continuousAt.tendsto.comp he
           apply tendsto_pi_nhds.mpr; intro u; apply tendsto_pi_nhds.mpr; intro v
           let X(i:Side)(x):= shout false (D i).val x (s i p) u v; let C:ℂ:= (L.val:ℂ)*Kit.slope L
           have hM(i x): Φ p x i u v=C*X i x :=by unfold Φ song C X; rw [Matrix.smul_apply]; exact congr_arg (· * X i x) (congr_arg (fun i:Side=>(i.val:ℂ)*(Kit.slope i:ℂ)) (e i))
           have he:= (shout_bill hp hv false (fun i:Side=> (D i).val) (fun i=> s i p)).tap u v; have hx:= (bring X (he.raise_price (fun i=>decay_le_one ..)) id).const_mul C
           have hL:= hx.add (tendsto_const_nhds (x:=A p u v)); rw [mul_zero,zero_add] at hL; refine hL.congr (fun i=>?_); dsimp only [id_eq]; rw [mul_sub,← hM,← hM, hh]; unfold Y; rw [sub_add_cancel]
     let U i:= wave g5 *∑ p:Site L,(Φ p (zerov i) i)ᴴ * wave g5*Φ p (zerov i) i; let V:=wave g5 *∑ p:Site L,(A p)ᴴ *wave g5*A p; have hv:Tendsto U atTop (𝓝 V):=(tendsto_finsetSum _ (fun p _=> (show Tendsto (fun i=> (Φ p (zerov i) i)ᴴ*wave g5 * Φ p (zerov i) i) atTop (𝓝 _) from (((hc p).star.mul_const _).mul (hc p))))).const_mul _ -- syntax
     have hr: ∀ i,Quixote (D i).val (zerov i)=U i:=by intro i; unfold Quixote U Φ; rw [← Equiv.sum_comp (s i)]
     have hp:V=(L.val:ℂ) • 1:=by
         let b:Side:=1; have hz:=congr_fun (congr_fun (fir (D b).val) chad) chad; apply Eq.trans _ (b:=Quixote (D b).val 0) ((fir (D b).val).trans (by rw [e b])); unfold V Quixote; rw [← Equiv.sum_comp (s b)]
         refine congr_arg _ (sum_congr rfl fun i _=>?_ ); rw [← hh i b]
     have ht:Tendsto (fun i=>U i chad chad) atTop (𝓝 (V chad chad)):=by
         let E:Bundle →L[ℂ] ℂ:=LinearMap.toContinuousLinearMap { toFun:=fun x=>x chad chad,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
         exact E.continuous.continuousAt.tendsto.comp hv
     rw [hp] at ht; simp_rw [hr]; simpa using ht
end rays
end YM.QCD.Finch
