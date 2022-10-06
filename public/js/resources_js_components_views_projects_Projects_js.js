"use strict";
(self["webpackChunk"] = self["webpackChunk"] || []).push([["resources_js_components_views_projects_Projects_js"],{

/***/ "./resources/js/components/views/projects/Projects.js":
/*!************************************************************!*\
  !*** ./resources/js/components/views/projects/Projects.js ***!
  \************************************************************/
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

__webpack_require__.r(__webpack_exports__);
/* harmony export */ __webpack_require__.d(__webpack_exports__, {
/* harmony export */   "default": () => (__WEBPACK_DEFAULT_EXPORT__)
/* harmony export */ });
/* harmony import */ var react__WEBPACK_IMPORTED_MODULE_0__ = __webpack_require__(/*! react */ "./node_modules/react/index.js");
/* harmony import */ var react__WEBPACK_IMPORTED_MODULE_0___default = /*#__PURE__*/__webpack_require__.n(react__WEBPACK_IMPORTED_MODULE_0__);
/* harmony import */ var react_data_table_component__WEBPACK_IMPORTED_MODULE_1__ = __webpack_require__(/*! react-data-table-component */ "./node_modules/react-data-table-component/dist/index.cjs.js");
/* harmony import */ var _common_components_CustomTable__WEBPACK_IMPORTED_MODULE_2__ = __webpack_require__(/*! ../../common-components/CustomTable */ "./resources/js/components/common-components/CustomTable.js");
/* harmony import */ var react_router_dom__WEBPACK_IMPORTED_MODULE_7__ = __webpack_require__(/*! react-router-dom */ "./node_modules/react-router-dom/dist/index.js");
/* harmony import */ var _helpers_fetchWrapper__WEBPACK_IMPORTED_MODULE_3__ = __webpack_require__(/*! ../../helpers/fetchWrapper */ "./resources/js/components/helpers/fetchWrapper.js");
/* harmony import */ var _coreui_react__WEBPACK_IMPORTED_MODULE_4__ = __webpack_require__(/*! @coreui/react */ "./node_modules/@coreui/react/dist/index.es.js");
/* harmony import */ var _helpers_common__WEBPACK_IMPORTED_MODULE_5__ = __webpack_require__(/*! ../../helpers/common */ "./resources/js/components/helpers/common.js");
/* harmony import */ var react_jsx_runtime__WEBPACK_IMPORTED_MODULE_6__ = __webpack_require__(/*! react/jsx-runtime */ "./node_modules/react/jsx-runtime.js");
function _slicedToArray(arr, i) { return _arrayWithHoles(arr) || _iterableToArrayLimit(arr, i) || _unsupportedIterableToArray(arr, i) || _nonIterableRest(); }

function _nonIterableRest() { throw new TypeError("Invalid attempt to destructure non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method."); }

function _unsupportedIterableToArray(o, minLen) { if (!o) return; if (typeof o === "string") return _arrayLikeToArray(o, minLen); var n = Object.prototype.toString.call(o).slice(8, -1); if (n === "Object" && o.constructor) n = o.constructor.name; if (n === "Map" || n === "Set") return Array.from(o); if (n === "Arguments" || /^(?:Ui|I)nt(?:8|16|32)(?:Clamped)?Array$/.test(n)) return _arrayLikeToArray(o, minLen); }

function _arrayLikeToArray(arr, len) { if (len == null || len > arr.length) len = arr.length; for (var i = 0, arr2 = new Array(len); i < len; i++) { arr2[i] = arr[i]; } return arr2; }

function _iterableToArrayLimit(arr, i) { var _i = arr == null ? null : typeof Symbol !== "undefined" && arr[Symbol.iterator] || arr["@@iterator"]; if (_i == null) return; var _arr = []; var _n = true; var _d = false; var _s, _e; try { for (_i = _i.call(arr); !(_n = (_s = _i.next()).done); _n = true) { _arr.push(_s.value); if (i && _arr.length === i) break; } } catch (err) { _d = true; _e = err; } finally { try { if (!_n && _i["return"] != null) _i["return"](); } finally { if (_d) throw _e; } } return _arr; }

function _arrayWithHoles(arr) { if (Array.isArray(arr)) return arr; }












var Projects = function Projects() {
  var _React$useState = react__WEBPACK_IMPORTED_MODULE_0___default().useState([]),
      _React$useState2 = _slicedToArray(_React$useState, 2),
      projects = _React$useState2[0],
      setProjects = _React$useState2[1];

  var fetchProjects = function fetchProjects() {
    _helpers_fetchWrapper__WEBPACK_IMPORTED_MODULE_3__["default"].get('/api/projects').then(function (response) {
      var data = response.data;

      if (data.status === 'success') {
        setProjects(data.projects);
      }
    })["catch"](function (error) {});
  };

  var handleDelete = function handleDelete(id) {
    (0,_helpers_common__WEBPACK_IMPORTED_MODULE_5__.swalConfirm)().then(function (result) {
      if (result.isConfirmed) {
        _helpers_fetchWrapper__WEBPACK_IMPORTED_MODULE_3__["default"]["delete"]('/api/projects/' + id).then(function (response) {
          var data = response.data;

          if (data.status === 'success') {
            (0,_helpers_common__WEBPACK_IMPORTED_MODULE_5__.swalSuccess)("Project deleted successfully");
            fetchProjects();
          } else {
            (0,_helpers_common__WEBPACK_IMPORTED_MODULE_5__.swalError)("Error deleting project");
          }
        })["catch"](function (error) {
          (0,_helpers_common__WEBPACK_IMPORTED_MODULE_5__.swalError)("Error deleting project");
        });
      }
    });
  };

  var columns = [{
    name: 'PROJECTS',
    selector: function selector(row) {
      return row.project_name;
    },
    sortable: true
  }, {
    name: 'SERVER ID',
    selector: function selector(row) {
      return row.server_id;
    },
    sortable: true
  }, {
    name: 'CHANNEL IDS',
    selector: function selector(row) {
      return row.channels.map(function (channel) {
        return channel.channel_id;
      }).join(',');
    },
    sortable: true
  }, {
    name: 'ACTIONS',
    selector: function selector(row) {
      return /*#__PURE__*/(0,react_jsx_runtime__WEBPACK_IMPORTED_MODULE_6__.jsxs)("div", {
        children: [/*#__PURE__*/(0,react_jsx_runtime__WEBPACK_IMPORTED_MODULE_6__.jsx)(react_router_dom__WEBPACK_IMPORTED_MODULE_7__.Link, {
          to: "/projects/".concat(row.id, "/edit"),
          className: "btn btn-primary btn-sm",
          children: /*#__PURE__*/(0,react_jsx_runtime__WEBPACK_IMPORTED_MODULE_6__.jsx)("i", {
            className: "fa fa-edit"
          })
        }), /*#__PURE__*/(0,react_jsx_runtime__WEBPACK_IMPORTED_MODULE_6__.jsx)(_coreui_react__WEBPACK_IMPORTED_MODULE_4__.CButton, {
          className: "btn btn-danger btn-sm mx-2",
          onClick: function onClick() {
            return handleDelete(row.id);
          },
          children: /*#__PURE__*/(0,react_jsx_runtime__WEBPACK_IMPORTED_MODULE_6__.jsx)("i", {
            className: "fa fa-trash"
          })
        })]
      });
    }
  }];
  (0,react__WEBPACK_IMPORTED_MODULE_0__.useEffect)(function () {
    fetchProjects();
  }, [projects.length]);
  return /*#__PURE__*/(0,react_jsx_runtime__WEBPACK_IMPORTED_MODULE_6__.jsx)(react_jsx_runtime__WEBPACK_IMPORTED_MODULE_6__.Fragment, {
    children: /*#__PURE__*/(0,react_jsx_runtime__WEBPACK_IMPORTED_MODULE_6__.jsx)(_common_components_CustomTable__WEBPACK_IMPORTED_MODULE_2__["default"], {
      title: "Projects",
      columns: columns,
      data: projects,
      createLink: "/projects/create"
    })
  });
};

/* harmony default export */ const __WEBPACK_DEFAULT_EXPORT__ = (Projects);

/***/ })

}]);