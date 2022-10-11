import React from 'react'
import { useSelector, useDispatch } from 'react-redux'

import {CImage, CSidebar, CSidebarBrand, CSidebarNav, CSidebarToggler} from '@coreui/react'
import CIcon from '@coreui/icons-react'

import { AppSidebarNav } from './AppSidebarNav'

import SimpleBar from 'simplebar-react'
import 'simplebar/dist/simplebar.min.css'

// sidebar nav config
import navigation from '../_nav'
import {logoNegative} from "../assets/brand/logo-negative";
import {sygnet} from "../assets/brand/sygnet";
import logo from "../assets/images/logo.png";

const AppSidebar = () => {
  const dispatch = useDispatch()
  const unfoldable = useSelector((state) => state.sidebarUnfoldable)
  const sidebarShow = useSelector((state) => state.sidebarShow)
    const user = useSelector(state => state.user);

    const navigationItems = navigation.filter((item) => {
        if (item.is_admin === 'true') {
            if (user && user.is_admin === 1) {
                return true;
            } else {
                return false;
            }
        } else {
            return true;
        }
    });

  return (
    <CSidebar
      position="fixed"
      unfoldable={unfoldable}
      visible={sidebarShow}
      onVisibleChange={(visible) => {
        dispatch({ type: 'set', sidebarShow: visible })
      }}
    >
      <CSidebarBrand className="d-none d-md-flex" to="/">
          <CImage src={logo} height={60} />
        {/*<CIcon className="sidebar-brand-full" icon={logoNegative} height={35} />*/}
        {/*<CIcon className="sidebar-brand-narrow" icon={sygnet} height={35} />*/}
      </CSidebarBrand>
      <CSidebarNav>
        <SimpleBar>
          <AppSidebarNav items={navigationItems} />
        </SimpleBar>
      </CSidebarNav>
      <CSidebarToggler
        className="d-none d-lg-flex"
        onClick={() => dispatch({ type: 'set', sidebarUnfoldable: !unfoldable })}
      />
    </CSidebar>
  )
}

export default React.memo(AppSidebar)
