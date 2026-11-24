import YM.Poised.Hemp
/-!
# Production of Principal spin payer.
Pre L.Cut all grades. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B A X E : Type}{d a k n m r:ℕ}{c l:Side}
namespace Pipes
open Set Cedar Ember Oval Cove Creek Stew PhysicalNext.JointLoad MultiNext.SignedSource MultiNext.SignedSource.Lyre Place Lining Lining.Ferry QCD.Brick
open YM.Next.Free Pressure Garden QCD.Fork Leaf Tee Flume Kit Run Laurent Newt
variable (P:Flight n m)(D:l.val=c.val * P.L.val)
variable (b:Cover) [Fintype B]
lemma inR_R {w: VectorD (Site l) B}(f: Faces (Site l)→ℝ)(g:B→ℝ)(P:BudgetPoint) (C:ℝ)(he:SeatD f g w C): Venture f g (P:=P) (o:=wrap l b) C (0,w):= ⟨⟨he.1,fun i=>(show ‖(0:su.Color)‖ ≤ _ from (norm_zero).le.trans (mul_nonneg he.1 (Lyre.width_pos ..).le))⟩,he⟩
lemma receipt (R K:ℕ)(hK:R≤K)(h:n≥4)(h':m≥4)(hk:R ≤ n-2) (M:ℝ)(ht:1≤M) :∃ C:ℝ,1≤C ∧∀ (c l:Side)(P:Flight n m)(H:l.val=c.val*P.L.val)(b:Cover)(u t:ℝ),0<u → 0<t →t ≤ M*u →∀ V: Support l,∀ S: BudgetPoint, ∀ k'≤3+2*R,
    let Q:=wrap l b; let p:=sliceL P H; Heritage S V b (purseX Q K u) (purseX (p.parent Q) K t) k' (0,flareV (proton P H)) (Kit.slope P.L) C:=by
    obtain ⟨C,hC,hY⟩:=towns K h h'
    obtain ⟨A,hA,hy⟩:= baggage K R hK; let v:= (4:ℝ)^K; let C₁:= A*C*M*v; have hv:1 ≤ v:=one_le_pow₀ (by norm_num); have hC' : 1 ≤ C₁:=one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA hC) ht) hv
    refine ⟨(R+1:ℕ)*C₁,one_le_mul_of_one_le_of_one_le (by simp) hC',?_⟩; intro c l P H b u t hU hT ht k S r hN Q p
    let f:=purseX Q K u; let g:=purseX (p.parent Q) K t; let X:= flareV (proton P H); let W(i: Fin (R+1)):= pathV b X i; let D:=C*Kit.slope P.L*t; let L:ℝ:= P.L.val; let z:=Kit.slope P.L; obtain ⟨hz,hZ⟩:= boxed1 P.L; have hL:1≤L:=Nat.one_le_cast.mpr P.L.property
    let F(i:Pipes.Shell): Flet (Faces (Site c))→L[ℝ] Alg (Faces (Site c)):= (beamW g).comp (ContinuousLinearMap.proj i)
    have hg i:0<g i:= purse_pos _ _ _ hT _ -- args
    let v' := rowsA b X; have hP(i:Pipes.Shell): drift K R D L⁻¹ (F i ∘ v'):=by
      intro j hj v; rw [← iter,Function.comp_apply,show Newt.iterate v' j=_ from hike b (proton P H) j]; change ‖beamW g _‖ ≤ _; rw [beam_price g (fun i=>(hg i).le)]; have hx:= hY c l P H j.reverse (by simpa using hj.trans hk) b v i t hT; 
      change capW g _≤ D*L⁻¹^(1+j.reverse.length)*(1+L⁻¹*size v)^K at hx; rw [List.length_reverse] at hx; exact hx
    have hF(i:Pipes.Shell):= hy (Alg (Faces (Site c))) D L hL (show 0≤D by unfold D; positivity) _ (hP i)
    have hp' (i:Pipes.Shell)(j:Fin (R+1))(x:Cover): capW g (symbols v' j x i) ≤ A*D*L⁻¹^(1+j.val)*(1+(Laurent.size x:ℝ))^K:=by
       rw [← beam_price g (fun t=>(hg t).le)]; change ‖F i (symbols v' j x)‖ ≤ _; unfold symbols; split; next hj=> apply le_trans _ ((hF i x).1 _ hj); exact le_of_eq (congr_arg norm (congr_fun (Pipes.patch (F i) v' j.val) (vector x))) -- definitional
       next hj=> rw [show F i (tail R v' x) =tail R (F i ∘ v') x from congr_fun (pin (F i) v' R) x]; exact ((hF i x).2).trans_eq (by rw [show j.val=R by omega])
    let Y(j:Fin (R+1)):Path l (Faces (Site c)) := (0,W j); let ψ(j:Fin (R+1)):= 3+2*j.val
    have hS(j:Fin (R+1)): SeatD f g (W j) (C₁*z^(ψ j)):=by
       apply (SeatD.from_weights _ _ _ _ (purse_pos Q K u hU) (fun t=>(hg t).le)).2; refine ⟨by unfold z; positivity,fun q=>?_⟩
       obtain ⟨⟨p,i⟩,rfl⟩:= (stretch (Site l)).surjective q; let a:= Beacon.offset b p; let d:ℕ:= separation p Q
       have hm:1+(size a:ℝ) ≤ 4*(1+(d:ℝ)):=by
          have h : size a ≤ 4*d:= trail_size ..; have hh:(size a:ℝ)≤4*(d:ℝ):=by exact_mod_cast h
          linarith
       apply le_trans (b:=capW g (symbols v' j a i)); · change capW g (asks _ p i) ≤ _; change capW g (asks (flats _) p i)≤ _; rw [invers]; unfold capW; simp only [Pi.smul_apply,norm_smul,frond, ap_one, one_mul]; exact le_rfl
       apply (hp' i j a).trans
       have hu:A*D ≤ A*C*M*z*u:=calc
          _ ≤ A*(C*z*(M*u)):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht (by unfold z; positivity)) (by positivity)
          _ = _:=by ring
       have hZ(z:ℕ):0≤L⁻¹^z:=by positivity
       apply (mul_le_mul (mul_le_mul_of_nonneg_right hu (by positivity)) (pow_le_pow_left₀ (by positivity) hm K) (by positivity) (by unfold z; positivity)).trans_eq
       unfold purseX; rw [life, show L⁻¹=z^2 from boxed_sq _]; unfold Heir.spine C₁ ψ v d; rw [mul_pow (4:ℝ)]; dsimp only; ring -- natural vars
    have hU : (∑ j,Y j)=(0,X):=Prod.ext (by rw [Prod.fst_sum]; simp [Y]) (by rw [Prod.snd_sum]; exact pathV_pay b X R)
    have he:= assembleH S k b f g (k:=r) Finset.univ Y ψ (fun i=>by unfold ψ; omega) (fun i=> inR_R b f g S _ (hS i)) (fun j hj=> inR_bu b X j k (by unfold ψ at hj; omega)) hz hZ (zero_le_one.trans hC')
    rwa [card_univ,Fintype.card_fin,hU] at he
end Pipes
end YM.Massive.Poised
