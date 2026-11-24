import YM.Vern.Buck
import YM.Vern.Socks
import YM.Vern.Song
import YM.Vern.Bear
set_option autoImplicit false
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Vern
open Function Set Filter Analysis MeasureTheory Lattice QCD QCD.Lat
open Massive Massive.UV Massive.Tarn Massive.Tarn.Choir Massive.Tarn.Choir.Strip Massive.Patria.Gall.Onyx
open Massive.Tarn.ChargeQ Massive.Poised.Plans.Stamp.Stair Massive.Gust
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix InnerProductSpace
open Sprig Intag.Sprig UV.Free Massive.Poised.Plans.Stamp Heron Iceberg Lobo NativeV
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K}{d:ℕ}
variable {φ:ℕ→ℕ}(hf:Foil P K T)(HQ:K.Harmony P φ)(E:Canopy P φ K)(X:Lanterns T E)
variable (V:Axis× Axis→ K.W)(hV: Persona T V)(J:Axle K (fun a b=>V (a,b))) (B:Vane J)
variable (r:ℝ)(hr:0<r)(s:ℝ)(z:IceT→ℝ)
set_option quotPrecheck false
local notation "H₁"=> ↥(seedP T 8)
local notation "H₂"=> ↥(seedP T 10)
local notation "N₁"=> ↥(seatP 8)
local notation "N₂"=> ↥(seatP 10)
variable (L:Tri→Module.End ℂ ↥(seatP 8))(L':Tri→Module.End ℂ ↥(seatP 10))
variable (F: ↥(seatP 8)≃ₗ[ℂ]↥(seedP T 8))(F': ↥(seatP 10)≃ₗ[ℂ]↥(seedP T 10))
variable (a:Axis)
variable (hF:Feasible hf HQ E X V hV J (d:=8) (Nat.le_refl _) s z L F)
variable (hW:Feasible hf HQ E X V hV J (d:=10) (by decide) s z L' F')
variable (e:Hail.RightAuth P.sym)
variable (f:Flavor 6)(he:z none ≠ z (some f))
-- orientation intertwine and evaluate.
noncomputable def Mango(f:Flavor 6)(i j:Tri):seatP 10:= geared _ ⟨hunt f i j,rotor f (lieu j) false i⟩ -- order
noncomputable def Pont(f:Flavor 6)(i:Tri):seatP 10:= geared _ ⟨rente f i,rotor f timeAxis true i⟩
local notation "R"=> metal hf HQ V hV J B r hr s
local notation "P'"=> dayV hf HQ V hV J B r hr s
noncomputable def glowZ(f:Flavor 6) (i j:Tri):seedP T 10:= F' (Mango f i j)
noncomputable def pearlZ(f: Flavor 6)(i:Tri):seedP T 10:= F' (Pont f i)
local notation "Tz"=> glowZ F' f
include e hW B hr
open Finset
lemma meetT : Olive (R) (z none) (z (some f)) (glowZ F' f):=by
    constructor
    · intro k i j; let H:=(fun i j:Tri=>Mango f i j); let x:=(z none:ℂ) • drive k (fun i=>H i j) i+ (z (some f):ℂ) • drive k (H i) j
      have h: omegaQ k z 10 (H i j).val=x.val:=by rw[show (H i j).val=projection (hunt f i j) from rfl,truss f k i j P.sym e]; unfold x drive; simp only [Submodule.coe_add,AddSubmonoidClass.coe_finsetSum,Submodule.coe_smul]; rfl
      refine Eq.trans (gramH hf HQ E X V hV J _ s z L' F' hW k (H i j) x h) ?_; unfold x; rw[map_add,map_smul,map_smul]; unfold drive; simp_rw [map_sum,map_smul]; rfl
    intro k i j; let y:= (charI k i :ℂ) • ((charI k j:ℂ) • (Mango f (roof k i) (roof k j))); have h:y.val=projection (P.sym.pin _ (SpinQ k) (hunt f i j)):=by unfold y; rw[Submodule.coe_smul,Submodule.coe_smul, tincture,map_smul,map_smul]; rfl
    refine Eq.trans (spinH hf HQ E X V hV J _ s z L' F' hW _ _ y (hunt f i j) (show (Mango f i j).val= _ from rfl) h) ?_; unfold y; rw[map_smul,map_smul]; rfl
lemma smears(k i: Tri) : (R).J k (pearlZ F' f i)=(z none:ℂ) • drive k (pearlZ F' f) i ∧ (R).K k (pearlZ F' f i)= τc k i • pearlZ F' f (roof k i):=by
    constructor
    · let H:= Pont f; let x:=(z none:ℂ) • drive k H i; have h: omegaQ k z 10 (H i).val=x.val:=by rw[show (H i).val=projection (rente f i) from rfl,atW f k i P.sym e]; unfold x drive; simp only[AddSubmonoidClass.coe_finsetSum,Submodule.coe_smul]; rfl
      refine Eq.trans (gramH hf HQ E X V hV J _ s z L' F' hW _ _ x h) ?_; unfold x drive; rw [map_smul,map_sum]; simp_rw[map_smul]; rfl
    let x:=(τc k i) • (Pont f (roof k i)); have h:x.val=projection (P.sym.pin _ (SpinQ k) (rente f i)):=by unfold x; rw[Submodule.coe_smul, cumin,map_smul]; rfl
    refine Eq.trans (spinH hf HQ E X V hV J _ s z L' F' hW _ _ x _ rfl h) ?_; unfold x; rw[map_smul]; rfl
include hF he
-- use Z cases all. wrapper independent
local notation "ψ" => (haze (R) (P') (glowZ F' f) a).comp (NativeV.strip (R) (P') a)
lemma nullOrig(u:seedP T 8):((haze (R) (P') (glowZ F' f) a).comp (NativeV.strip (R) (P') a)) u =0:=by
     let H : (seedP T 8) →ₗ[ℂ]ℂ:= ψ; let M:Qa 8→ₗ[ℂ]ℂ:= H ∘ₗ F.toLinearMap ∘ₗ geared 8; obtain ⟨x,rfl⟩:= F.surjective u; obtain ⟨x,rfl⟩:=gained x; change M x=0; let S:= LinearMap.range ((Qa 8).subtype.comp M.ker.subtype);
     have hm (x:Qa 8): x.val∈S ↔ M x=0:=by
           constructor
           · rintro ⟨u,h⟩; have hz:u.val=x:=Subtype.ext h; exact hz ▸ u.property
           intro hz; exact ⟨⟨x,hz⟩,rfl⟩
     refine (hm _).1 (?_ : _∈S); let O: (seedP T 8) →ₗ[ℂ]ℂ:= (ψ); have hQ:= meetT hf HQ E X V hV J B r hr s z L' F' hW e f
     have ht(Y:Tri→Tri→seedP T 8)(b:ℂ)(hs:Nation R P' Y b)(i j:Tri): O (Y i j)=0:=by
            -- fin_cases a replacing H,O
            unfold O; fin_cases a<;> first|exact ZK0 _ _ _ _ _ hQ Y b he hs i j|exact ZK1 _ _ _ _ _ hQ Y b he hs i j|exact ZK2 _ _ _ _ _ hQ Y b he hs i j|exact ZK3 _ _ _ _ _ hQ Y b he hs i j
     have hg(Y:Tri→seedP T 8)(b:ℝ)(hs:Spirit R P' Y b)(i:Tri): O (Y i)=0:=by unfold O; fin_cases a <;> first| exact TK0 _ _ _ _ _ hQ _ b he hs i | exact TK1 _ _ _ _ _ hQ _ b he hs i | exact TK2 _ _ _ _ _ hQ _ b he hs i | exact TK3 _ _ _ _ _ hQ _ b he hs i
     refine earnest S P.sym (fun b p h=> ?_) (fun b p h=>?_) (fun b p h hl=>?_) x.property
     · let p':Qa 8:=⟨p,h.q⟩; let v:=geared _ p'; let W:=F v; have hw:= soils hf HQ E X V hV J _ s z L F hF h v rfl e; apply (hm p').2; let Q(i j:Tri): seedP T 8:= if i=j then W else 0; have hp:Nation (R) (P') Q 0:=vacF (R) (P') W (fun i=> (hw i).2) (fun i=>(hw i).1); exact ht Q 0 hp 0 0
     · let x(i:Tri):Qa 8:=⟨p i,h.q i⟩; let y(i):=geared _ (x i); let W(i):= F (y i); have hw:= spill hf HQ E X V hV J _ s z L F hF h y (fun _=>rfl) e; have h:Spirit (R) (P') W (z b):=⟨fun i j=>(hw i j).1,fun i j=>(hw i j).2⟩; exact fun i=>(hm (x i)).mpr (hg W (z b) h i)
     let x(i j:Tri): Qa 8:=⟨p i j,h.q i j⟩; let y(i j):=geared _ (x i j); let W(i j):= F (y i j); have hw:= sprout hf HQ E X V hV J _ s z L F hF h y (fun i j=>rfl) e; have h:Nation (R) (P') W (z b):=⟨fun i j k=>(hw i j k).1,fun i j k=>(hw i j k).2,fun i j=>congr_arg F (congr_arg (geared _) (Subtype.ext (hl j i)))⟩; exact fun i j=>(hm (x i j)).mpr (ht W (z b) h i j)
end YM.Vern
#print axioms YM.Vern.nullOrig
#print axioms YM.Vern.meetT
#print axioms YM.Vern.smears
