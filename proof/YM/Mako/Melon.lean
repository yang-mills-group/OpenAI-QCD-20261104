import YM.Mako.Pan
set_option maxHeartbeats 600000
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Set Function Filter Analysis Lattice QCD QCD.Lat MeasureTheory
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates
open scoped YM.Iceberg
open Work.A01
variable {C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{K:Choir}{T:Pollens P K}{d:ℕ}
variable {E:Canopy P φ K}{X:Lanterns T E}{W:Axis×Axis→ K.W} {A: Axle K (fun a b=>W (a,b))}{I:ℕ→ℕ} (J:Glacier T E X W A I)(H:Foil P K T)(HK:K.Domestic)(hd:8 ≤ d)
include H HK
lemma peels {n:ℕ}(v:Points (n+1))(y:E4)(hy:Points.cons y v∈conf (n+2)) (q:K.W)(p: Fin n→ K.W): K.total (n+2) (Points.cons y v) (Fin.cons q (Fin.cons (lampU P K) p))=K.total (n+1) (Points.cons y (Points.tail v)) (Fin.cons q p):=by
     rw[←grooved,←grooved]; let P':= (lampU P K); let l:Strip K:= [(y,q)]; let G:= grove K p (Points.tail v); let V:= Points.cons y v; have he: grove K (Fin.cons q (Fin.cons P' p)) V=l++ (v 0,P')::G:=by rw[grove,List.ofFn_succ]; simp only [V,Points.cons,points_apply,Fin.cons_zero, Fin.cons_succ]; rw[List.ofFn_succ]; rfl
     rw [show grove K (Fin.cons q (Fin.cons (lampU P K) p)) (Points.cons y v)=_ from he]; have hz: Strip.distinct (l++(v 0,P')::G):=by rw[←he]; exact (garden ..).2 hy
     refine (unit_point HK H _ _ _ hz).trans ?_ ; congr 1; unfold grove; rw[List.ofFn_succ]; rfl
include J
lemma tapsX (g:Ortho.Skew) : A.jet g (lampU P K)=0:=by
     apply detected H; intro n p x hx; obtain ⟨χ,hχ⟩:= Work.A01.exists_window x hx
     let U:= lampU P K; let w:= orbital g (x 0); let B:Axis→Axis→K.W:= fun a b=>W (a,b)
     have hW: Safe K B:=⟨J.n.tense.sym,soma W J.n⟩
     rw[map_zero, ← A.relation g _ n x χ hx hχ]
     have h0 (y:E4)(hy:y∈tsupport χ): Points.cons y (Points.tail x)∈conf _:=by refine conf_cons (Points.tail_in hx) fun i he=>?_ ; exact hχ.2.2.2 i (he ▸ hy)
     have he(a b:Axis)(y:E4): termG B χ w x (Fin.cons U p) a b y= D (basis a) χ y • (w y b • K.total _ (Points.cons y (Points.tail x)) (Fin.cons (B a b) p)):=by
            by_cases hp: D (basis a) χ y=0; · simp [termG,hp]
            unfold termG; rw[peels H HK x y (Work.A01.separated_of_D hx hχ hp)]; simp [Complex.real_smul,mul_assoc]
     have ht(a:Axis): (∑ b,∫ y, termG B χ w x (Fin.cons U p) a b y)= ∫ y, D (basis a) χ y • currentG B w (Points.tail x) p a y:=by
            rw[← integral_finsetSum _ (fun b _=> termG_integrable B χ w x (Fin.cons U p) HK hx hχ a b (smooth_orbital g (x 0) b).continuous)]; simp_rw[he,currentG,Finset.smul_sum]
     change -(∑ a:Axis, ∑ b:Axis,∫ y, termG B χ w x (Fin.cons U p) a b y)= _; simp_rw [ht]; exact Gust.cutoff_zero HK B hW w (smooth_orbital g (x 0)) (killing_orbital g (x 0)) _ p χ hχ.1 hχ.2.1 h0
omit J HK H
lemma u_one {δ:RawSym}(z:Roof δ)(p:EuPin): caravan z d p (projection (δ.unit d))=projection (δ.unit d):=by
     rw[clanP]; apply congr_arg; apply Subtype.ext; rw[δ.pinActs,δ.unitActs]; unfold UV.pinAct UV.unit; rw [TensorProduct.map_tmul]; exact congr_arg₂ _ (map_one (Labels.rotated p.coord)) (map_one (twistPins d p))
lemma fcore(g:Ortho.Skew)(p:Roof P.sym): rain g d (projection (P.sym.unit d))=0:=by
     let v:= projection (P.sym.unit d); apply (chime g (tour g) p v).unique; apply (hasDerivAt_const (x:=(0:ℝ)) v).congr_of_eventuallyEq; exact Eventually.of_forall (fun i=> u_one p _)
end YM.Mako
#print axioms YM.Mako.tapsX
#print axioms YM.Mako.fcore
